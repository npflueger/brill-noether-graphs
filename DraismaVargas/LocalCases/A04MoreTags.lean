import DraismaVargas.LocalCases.A04FourTags
import DraismaVargas.LocalCases.W2PArbitraryIncomingExit
import DraismaVargas.LocalCases.W2MkkArbitraryExit
import DraismaVargas.LocalCases.W2MkkStableIncidence
import DraismaVargas.LocalCases.W3FourStableIncidence

/-!
# Routed walls: the wall dispatcher and the full-dimensional supply on further tags

`A04FourTags` defines `FullDimSupply` -- the two gated full-dimensional fields
of `WallProgress.presentedProgressOfWallInputs` at one `WallProgress.WallInput`
-- and inhabits it for `w3Nd2CoarseFine`, `w3Nd3CoarseFine` and `w4`.  This
file does the same for `w2P`, `w2Mkk` in both orientations and `w3Four`, adds
each tag's **incoming** side in the shape
`A04FourTags.presentedProgressOfSupplies` asks for, and bundles the whole
per-wall input as `RoutedWall`, so that the dispatcher is fed by actual
local-case data rather than by seven parallel families of hypotheses.

## What is here

| tag | wall input | supply | carried |
|---|---|---|---|
| `w2P` | `ofW2P` (`WallInput.ofTrivalent` on `W2PArbitraryExit.family`) | `w2PSupply` | `hChart` |
| `w2Mkk` II.2.1.M | `ofW2MkkFirst` (`WallInput.ofGauge` on `W2MkkArbitraryExit.firstGaugeFamily`) | `mkkFirstSupply` | `hChart` |
| `w2Mkk` II.2.2.M | `ofW2MkkSecond` (`ofGauge` on `secondGaugeFamily`) | `mkkSecondSupply` | `hChart` |
| `w3Four` | `ofFourHonest` (`ofGauge` on `figure28HonestFamily`) | `w3FourSupply` | `certificate`, `memberGenus`, `hChart` |
| `w3Nd2CoarseFine` | `W3WallInput.ofNd2CoarseFine` | `A04FourTags.nd2Supply` | the incoming position, its nonsingularity, `hChart` |
| `w3Nd3CoarseFine` | `W3WallInput.ofNd3CoarseFine` | `A04FourTags.nd3Supply` | the incoming position, its nonsingularity, `hChart` |
| `w4` | `A04FourTags.ofFourValentHonest` | `A04FourTags.w4Supply` | the incoming position, its nonsingularity, `hChart` |

`hChart` is the **state--classifier equation** and nothing else: that the chart
the march currently occupies is the identified incoming member's own honest
length matrix.  It is one named hypothesis per tag, never more, because it is not
local-case data: it relates the state of the march to the classification of the
wall (`WallProgress` §3), and is supplied by the march, not by the local case.

## Three inputs that need no hypothesis

1. **`hW25Nodup`.**  Every one of the seven families presents its members by
   `W4StableSource.StableLengthMatrixLabelling.presentation`, whose row list is a
   `List.filter` of `Finset.univ.toList`.  `nodup_labelling_path` (§0) is the
   whole proof, `RoutedWall.HonestlyPresented` the property, and no case data
   enters; in particular no case-by-case appeal to
   `PresentationDecomposition.Decomposes.nodup` is needed.
2. **`w2Mkk`'s remote dictionary.**  `W2MkkArbitraryExit.RemoteDictionary` is
   `Nonempty (StableGraphIncidence.Equivalence data (swapRelabeling ...).apply)`
   for an arbitrary compatible global sheet relabelling, and
   `StableGraphIncidence.sheetRelabel` is that equivalence;
   `GluingDatum.SheetRelabeling.sourceGraphLaplacianEquiv` is the matching genus
   receipt.  `mkkFirstDictionary`/`mkkFirstMemberGenus` are those two lines, so
   `mkkFirstSupply` and `mkkSecondSupply` carry **no** condition.  The module
   `SheetRelabelIncidence` states the same pair under its own names; this file
   does not import it.
3. **`w2P`'s and `w2Mkk`'s incoming determinant.**
   `W2PArbitraryExit.outgoingLabelling_self` and
   `W2MkkArbitraryExit.squareMatrix_self` make the identified member's own
   honest square matrix literally its own, so `hW25IncomingNonzero` is
   `incomingFD.det_ne_zero` and `hW25IncomingMatrix` is `hChart` transported.

## What is carried

* `w3Four`: `certificate` and `memberGenus` -- see the note at §5.  They are
  supplied, at the same members as the honest receipts, by
  `W3FourRegrownColumnSeam.exists_memberCertificates`, and
  `TrackedWallProgressMore.routedW3FourHonest` composes the two.
* `w3Nd2CoarseFine`, `w3Nd3CoarseFine`, `w4`: the incoming position with its
  nonsingularity and matrix identity.  Those tags' incoming normalisations are
  proved with their own cases (for `w3Nd3CoarseFine`, in `W3Nd3ArbitraryExit`);
  the constructors `routedNd2`, `routedNd3`, `routedW4` take them as arguments in
  exactly the shape `RoutedWall` stores.
* every tag: `hChart`, and `hwallColumn` -- that the family's regrown column is
  the coordinate the march crosses.  `ofW2P_family_wallColumn` and
  `mkkFirstFamily_wallColumn` say what that column is in each case (the
  identified member's own wall occurrence); the arbitrary-incoming matching of
  each case identifies that occurrence with the original contracted column.

## The tags routed in other modules

The remaining four tags are routed in their own modules, each on an honest
family built for the purpose:

* `w3Shift` in `A04ShiftWiring`, on `W3ShiftHonestBalance.limitRows` (limit rows
  at an arbitrary `StableLengthMatrixLabelling` of one member, the analogue of
  `W3Nd3CommonBalance.labelling`/`squareMatrix`/`columnEquiv`/`wallColumn`),
  with `W3ShiftGraphData.between` as the `StableGraphIncidence.Equivalence`
  between the two members of the pair;
* `w2M11` in `A04M11Wiring`, on `M11HonestGaugeFamily.gaugeFamily`, and `w2M1k`
  in `A04M1kWiring`, on the gauge families of `W2M1kGaugeFamily` (one per
  orientation): the balanced families of these two cases (for `w2M11`,
  `M11CommonBalance.family`) are `BalancedGlobal.Family`s, while a wall input
  needs the gauge form `BalancedGlobal.GaugeFamily`;
* `w2R1` in `A04R1Wiring`, on `W2R1GraphData.family`.  The split-census family
  of `w2R1` presents its candidates by the raw census paths rather than by honest
  presentations, so, as for `WallProgress.WallInput.ofFourValent`, the
  full-dimensional supply cannot be literal on it.
-/
namespace DraismaVargas.LocalCases.A04MoreTags

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ClassifiedContinuation
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.WallProgress
open DraismaVargas.LocalCases.A04FourTags (FullDimSupply)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {wall : coordinate}

/-! ## 0.  Two seams used by every honest family -/

section Seams

variable {target : CFGraph} {datum : GluingDatum target degree}

omit [Fintype coordinate] in
/-- **Every honest stable labelling has duplicate-free rows.**  This is the
hypothesis `hW25Nodup` of `A04FourTags.presentedProgressOfSupplies`, for any family
whose presentations are `StableLengthMatrixLabelling.presentation`s: the row
list is a `List.filter` of `Finset.univ.toList`, and a filter of a duplicate-free
list is duplicate-free.  No case data enters. -/
theorem nodup_labelling_path
    (labelling : StableLengthMatrixLabelling datum coordinate) (row : coordinate) :
    ((StableLengthMatrixLabelling.presentation labelling).path row).Nodup := by
  classical
  change (labelling.path row).Nodup
  unfold StableLengthMatrixLabelling.path
  exact List.Nodup.filter _ (Finset.nodup_toList _)

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- A length-matrix presentation is its two fields. -/
theorem presentation_ext {p q : datum.LengthMatrixPresentation coordinate}
    (hTarget : p.targetEdge = q.targetEdge) (hPath : p.path = q.path) : p = q := by
  cases p; cases q; cases hTarget; cases hPath; rfl

variable {coordinate' : Type} [Fintype coordinate'] [DecidableEq coordinate']

/-- **Move an honest stable labelling to a different coordinate labelling.**  The
labelling analogue of `ClassifierInterface.reindex`: the column dictionary is
precomposed and the row dictionary postcomposed with the same equivalence.  It
is needed because the `w3Four` exits are stated over `Option target.edges`, the
coordinate Figure 28's members are built in, while a `WallProgress.WallInput`
lives over the march's ambient coordinate. -/
def reindexLabelling (relabel : coordinate ≃ coordinate')
    (labelling : StableLengthMatrixLabelling datum coordinate') :
    StableLengthMatrixLabelling datum coordinate where
  targetEdge := relabel.trans labelling.targetEdge
  row := labelling.row.trans relabel.symm

omit [Fintype coordinate] [Fintype coordinate'] in
/-- **and it presents the reindexed presentation.**  The row list at a coordinate
is a filter over the same `Finset.univ.toList`, and the two filter predicates are
`Equiv.symm_apply_eq` apart. -/
theorem reindexLabelling_presentation (relabel : coordinate ≃ coordinate')
    (labelling : StableLengthMatrixLabelling datum coordinate') :
    StableLengthMatrixLabelling.presentation (reindexLabelling relabel labelling) =
      ClassifierInterface.reindex relabel
        (StableLengthMatrixLabelling.presentation labelling) := by
  classical
  refine presentation_ext rfl (funext fun row ↦ ?_)
  show (reindexLabelling relabel labelling).path row = labelling.path (relabel row)
  unfold StableLengthMatrixLabelling.path
  refine List.filter_congr fun edge _ ↦ decide_eq_decide.mpr ?_
  constructor
  · rintro ⟨hSurvives, hrow⟩
    exact ⟨hSurvives, (Equiv.symm_apply_eq relabel).mp hrow⟩
  · rintro ⟨hSurvives, hrow⟩
    exact ⟨hSurvives, (Equiv.symm_apply_eq relabel).mpr hrow⟩

omit [Fintype coordinate] [Fintype coordinate'] in
/-- Hence its length matrix is the corresponding submatrix. -/
theorem reindexLabelling_matrix (relabel : coordinate ≃ coordinate')
    (labelling : StableLengthMatrixLabelling datum coordinate') :
    GluingDatum.LengthMatrixPresentation.matrix
        (StableLengthMatrixLabelling.presentation (reindexLabelling relabel labelling)) =
      (GluingDatum.LengthMatrixPresentation.matrix
        (StableLengthMatrixLabelling.presentation labelling)).submatrix relabel relabel := by
  rw [reindexLabelling_presentation, ClassifierInterface.matrix_reindex]

/-- and its determinant is unchanged. -/
theorem reindexLabelling_det (relabel : coordinate ≃ coordinate')
    (labelling : StableLengthMatrixLabelling datum coordinate') :
    (GluingDatum.LengthMatrixPresentation.matrix
        (StableLengthMatrixLabelling.presentation
          (reindexLabelling relabel labelling))).det =
      (GluingDatum.LengthMatrixPresentation.matrix
        (StableLengthMatrixLabelling.presentation labelling)).det := by
  rw [reindexLabelling_presentation, ClassifierInterface.det_matrix_reindex]

/-- **A full-dimensional presentation moved to a different coordinate
labelling.**  Only `labelling` and `det_ne_zero` depend on the coordinate; the
six combinatorial fields are carried over verbatim. -/
noncomputable def reindexFullDim (relabel : coordinate ≃ coordinate')
    (fd : FullDimensionalSourcePresentation datum coordinate') :
    FullDimensionalSourcePresentation datum coordinate where
  valid := fd.valid
  targetConnected := fd.targetConnected
  targetGenus := fd.targetGenus
  saturated := fd.saturated
  labelling := reindexLabelling relabel fd.labelling
  det_ne_zero := by
    rw [reindexLabelling_det]; exact fd.det_ne_zero
  trivalent := fd.trivalent
  pathEnds := fd.pathEnds

@[simp] theorem reindexFullDim_labelling (relabel : coordinate ≃ coordinate')
    (fd : FullDimensionalSourcePresentation datum coordinate') :
    (reindexFullDim relabel fd).labelling = reindexLabelling relabel fd.labelling := rfl

end Seams


/-! ## 1.  What one wall owes, bundled -/

section Routed

open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.SemanticAtlasMarch

/-- **Everything the march needs at one wall coordinate.**  The dispatcher's
wall input and its duplicate-free rows, the gated full-dimensional pair on it
(`A04FourTags.FullDimSupply`), and the three state–classifier facts, all against
one chart matrix.  A family of these at every coordinate is exactly the
arguments of `A04FourTags.presentedProgressOfSupplies` other than the state
itself and the genericity hypothesis `hA02Generic`, which is not per-wall. -/
structure RoutedWall (degree : ℕ) (coordinate : Type) [Fintype coordinate]
    [DecidableEq coordinate] (chart : Matrix coordinate coordinate ℚ)
    (wall : coordinate) where
  /-- The dispatcher's wall input at this coordinate. -/
  input : WallInput degree coordinate wall
  /-- The gated full-dimensional pair on it. -/
  supply : FullDimSupply input
  /-- Duplicate-free rows (`hW25Nodup`). -/
  nodup : ∀ (i : Fin input.case.arity) (row : coordinate),
    ((input.family.presentation i).path row).Nodup
  /-- `hW25Incoming`: the member the march currently occupies. -/
  incoming : Fin input.case.arity
  /-- The incoming member is nonsingular (`hW25IncomingNonzero`). -/
  incomingNonzero : (GluingDatum.LengthMatrixPresentation.matrix
    (input.family.presentation incoming)).det ≠ 0
  /-- The incoming member's matrix is the chart (`hW25IncomingMatrix`). -/
  incomingMatrix : GluingDatum.LengthMatrixPresentation.matrix
    (input.family.presentation incoming) = chart

namespace RoutedWall

/-- **A wall input whose family carries the members' own honest stable
labellings.**  All seven routed-and-supplied tags have this, and it is the only
thing `hW25Nodup` needs (`§0`). -/
def HonestlyPresented (input : WallInput degree coordinate wall) : Prop :=
  ∀ i : Fin input.case.arity,
    ∃ labelling : StableLengthMatrixLabelling (input.family.candidate i).datum coordinate,
      input.family.presentation i = StableLengthMatrixLabelling.presentation labelling

theorem nodup_of_honestlyPresented {input : WallInput degree coordinate wall}
    (honest : HonestlyPresented input) (i : Fin input.case.arity) (row : coordinate) :
    ((input.family.presentation i).path row).Nodup := by
  obtain ⟨labelling, hlabelling⟩ := honest i
  rw [hlabelling]
  exact nodup_labelling_path labelling row

/-- **The generic constructor.**  Every tag below is this, with the fields it
can discharge discharged. -/
noncomputable def ofSupply {chart : Matrix coordinate coordinate ℚ}
    (input : WallInput degree coordinate wall) (supply : FullDimSupply input)
    (nodup : ∀ (i : Fin input.case.arity) (row : coordinate),
      ((input.family.presentation i).path row).Nodup)
    (incoming : Fin input.case.arity)
    (incomingNonzero : (GluingDatum.LengthMatrixPresentation.matrix
      (input.family.presentation incoming)).det ≠ 0)
    (incomingMatrix : GluingDatum.LengthMatrixPresentation.matrix
      (input.family.presentation incoming) = chart) :
    RoutedWall degree coordinate chart wall :=
  { input := input, supply := supply, nodup := nodup, incoming := incoming,
    incomingNonzero := incomingNonzero, incomingMatrix := incomingMatrix }

/-- and the same with `hW25Nodup` read off honesty. -/
noncomputable def ofHonestSupply {chart : Matrix coordinate coordinate ℚ}
    (input : WallInput degree coordinate wall) (supply : FullDimSupply input)
    (honest : HonestlyPresented input)
    (incoming : Fin input.case.arity)
    (incomingNonzero : (GluingDatum.LengthMatrixPresentation.matrix
      (input.family.presentation incoming)).det ≠ 0)
    (incomingMatrix : GluingDatum.LengthMatrixPresentation.matrix
      (input.family.presentation incoming) = chart) :
    RoutedWall degree coordinate chart wall :=
  ofSupply input supply (nodup_of_honestlyPresented honest) incoming incomingNonzero
    incomingMatrix

end RoutedWall

variable {baseStart baseFinish : coordinate → ℚ}

/-- **Presented progress from a routed wall at every first wall.**
`A04FourTags.presentedProgressOfSupplies` generalised: the state–classifier
triple is not a separate family of hypotheses, as it is there, but is carried by each
wall's own bundle, so the only argument left beside the bundles is the
genericity hypothesis `hA02Generic`.  The bundles are asked only where
`current.FirstWall` holds -- the coordinate the march crosses.

This is `WallProgress.presentedProgressOfWallInputs` with every per-wall
argument discharged from local-case data; see §7 for which tags inhabit
`RoutedWall` and on what. -/
noncomputable def presentedProgressOfRoutedWalls
    (current : State degree (atlasChartMatrix coordinate degree) baseStart baseFinish)
    (routed : ∀ (wall : coordinate), current.FirstWall wall →
      RoutedWall degree coordinate
        (atlasChartMatrix coordinate degree current.toMatrixState.label) wall)
    (hA02Generic : SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish) :
    current.PresentedProgress :=
  A04FourTags.presentedProgressOfSupplies current
    (fun wall hw ↦ (routed wall hw).input)
    (fun wall hw ↦ (routed wall hw).supply) (fun wall hw ↦ (routed wall hw).nodup)
    hA02Generic
    (fun wall hw ↦ (routed wall hw).incoming)
    (fun wall hw ↦ (routed wall hw).incomingNonzero)
    (fun wall hw ↦ (routed wall hw).incomingMatrix)

end Routed

/-! ## 2.  `w2P` -/

section W2P

open W2PSourceCandidates

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wallVertex}
  {block : WallBlock data wallVertex}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  (input : W2SourceInput data star) (shape : Shape profile)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    (W2PCommonBalance.members profile shape incoming).datum coordinate)

/-- **Figure 35's wall input.** -/
noncomputable def ofW2P
    (hwallColumn :
      (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofTrivalent (W2PArbitraryExit.family input shape incoming incomingFD)
    input.valid SourceCase.w2P rfl hwallColumn hConnected hGenus root

@[simp] theorem ofW2P_case
    (hwallColumn :
      (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW2P (wall := wall) input shape hConnected hGenus incoming incomingFD
      hwallColumn root).case = SourceCase.w2P := rfl

/-- **The full-dimensional supply for `w2P`.** -/
noncomputable def w2PSupply
    (hwallColumn :
      (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2P (wall := wall) input shape hConnected hGenus incoming
      incomingFD hwallColumn root) where
  fullDim := W2PArbitraryExit.familyFullDim input shape hConnected hGenus incoming
    incomingFD
  presentation_eq := W2PArbitraryExit.familyFullDim_presentation input shape hConnected
    hGenus incoming incomingFD

/-- **The `w2P` family presents the identified incoming member by its own honest
labelling.**  `W2PArbitraryExit.outgoingLabelling_self`: transport to the common
first member and back cancels both equivalences. -/
theorem ofW2P_presentation_incoming
    (hwallColumn :
      (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW2P (wall := wall) input shape hConnected hGenus incoming incomingFD
        hwallColumn root).family.presentation incoming =
      StableLengthMatrixLabelling.presentation incomingFD.labelling := by
  change (W2PArbitraryExit.outgoingLabelling input shape incoming incomingFD
    incoming).presentation = _
  rw [W2PArbitraryExit.outgoingLabelling_self input shape incoming incomingFD]

/-- **`hW25IncomingNonzero` for `w2P`.**  `W2PArbitraryExit.incomingDet_ne_zero`. -/
theorem ofW2P_incomingNonzero
    (hwallColumn :
      (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((ofW2P (wall := wall) input shape hConnected hGenus incoming incomingFD
        hwallColumn root).family.presentation incoming)).det ≠ 0 := by
  rw [ofW2P_presentation_incoming input shape hConnected hGenus incoming incomingFD
    hwallColumn root]
  exact incomingFD.det_ne_zero

/-- **`hW25IncomingMatrix` for `w2P`, modulo the state–classifier equation.**
`hChart` is the whole of what is not local-case data: that the chart the march
currently occupies is the identified member's own honest length matrix.  It is
the single named hypothesis of this tag's incoming side; everything else is
`outgoingLabelling_self`. -/
theorem ofW2P_incomingMatrix
    (hwallColumn :
      (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2P (wall := wall) input shape hConnected hGenus incoming incomingFD
          hwallColumn root).family.presentation incoming) = chart := by
  rw [ofW2P_presentation_incoming input shape hConnected hGenus incoming incomingFD
    hwallColumn root]
  exact hChart

/-- **`hW25Nodup` for `w2P`.**  The family's presentations are the honest
labellings' own, so §0 applies with no case data. -/
theorem ofW2P_nodup
    (hwallColumn :
      (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) (row : coordinate) :
    (((ofW2P (wall := wall) input shape hConnected hGenus incoming incomingFD
      hwallColumn root).family.presentation i).path row).Nodup :=
  nodup_labelling_path
    (W2PArbitraryExit.outgoingLabelling input shape incoming incomingFD i) row

/-- The `w2P` family is honestly presented. -/
theorem ofW2P_honestlyPresented
    (hwallColumn :
      (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (ofW2P (wall := wall) input shape hConnected hGenus
      incoming incomingFD hwallColumn root) :=
  fun i ↦ ⟨W2PArbitraryExit.outgoingLabelling input shape incoming incomingFD i, rfl⟩

/-- **`w2P` as a routed wall.**  `chart` is the march's current chart and
`hChart` the state–classifier equation, the one thing not local-case data. -/
noncomputable def routedW2P
    (hwallColumn :
      (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply
    (ofW2P (wall := wall) input shape hConnected hGenus incoming incomingFD hwallColumn
      root)
    (w2PSupply input shape hConnected hGenus incoming incomingFD hwallColumn root)
    (ofW2P_honestlyPresented input shape hConnected hGenus incoming incomingFD hwallColumn
      root)
    incoming
    (ofW2P_incomingNonzero input shape hConnected hGenus incoming incomingFD hwallColumn
      root)
    (ofW2P_incomingMatrix input shape hConnected hGenus incoming incomingFD hwallColumn
      root chart hChart)

/-! ### Where the incoming position comes from

The arbitrary-incoming matching for `w2P` (`W2PIncomingMatching.exists_member_normalization`,
restated in the original coordinates in `W2PArbitraryIncomingExit`) says an
arbitrary incoming `w2P` cover **is** a named Figure 35 member carrying an honest
presentation in the original coordinates.  Its position is `hW25Incoming`, its
member presentation is the `incomingFD` above, and its wall clause is exactly
this family's regrown column, so `hwallColumn` is the statement that the march's
crossed coordinate is the original contracted column. -/

/-- The `w2P` family's regrown column, read on the identified member's own
occurrence dictionary. -/
theorem ofW2P_family_wallColumn :
    (W2PArbitraryExit.family input shape incoming incomingFD).wallColumn =
      incomingFD.labelling.targetEdge.symm
        (W2PCommonBalance.columnEquiv profile shape incoming none) := by
  show ((incomingFD.labelling.targetEdge.trans
      ((W2PCommonBalance.columnEquiv profile shape incoming).symm.trans
        (W2PCommonBalance.columnEquiv profile shape 0))).trans
      (W2PCommonBalance.columnEquiv profile shape 0).symm).symm none = _
  refine (Equiv.symm_apply_eq _).mpr ?_
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

end W2P

/-! ## 3.  `w2Mkk`, Base II.2.1.M -/

section W2MkkFirst

open W2MkkSourceCandidates

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wallVertex}
  {block : WallBlock data wallVertex}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  (input : W2SourceInput data star) (shape : Shape profile)
  (member : FirstMember profile) (distinguished : Fin degree)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
      hGenus).member incoming).datum coordinate)

/-- Figure 34's honest family in the identified member's own square
coordinates, Base II.2.1.M. -/
noncomputable def mkkFirstFamily :
    GaugeFamily (coordinate := coordinate) 3 data wallVertex :=
  W2MkkArbitraryExit.firstGaugeFamily input shape distinguished hConnected hGenus member
    (W2MkkArbitraryExit.initialLabelling
      (W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus) incoming incomingFD)

/-- **Figure 34's wall input, Base II.2.1.M.**  Gauge-mixed: position `1` lives
over the branch-swapped copy, which is exactly what `WallInput.ofGauge` exists
for. -/
noncomputable def ofW2MkkFirst
    (hwallColumn : (mkkFirstFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofGauge (mkkFirstFamily input shape member distinguished hConnected hGenus
    incoming incomingFD) input.valid SourceCase.w2Mkk rfl hwallColumn hConnected hGenus
    root

@[simp] theorem ofW2MkkFirst_case
    (hwallColumn : (mkkFirstFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW2MkkFirst (wall := wall) input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root).case = SourceCase.w2Mkk := rfl

/-- Figure 34's three outgoing presentations in the Base II.2.1.M orientation,
one `W2MkkStableIncidence.presentationAt` per member.  `dictionary` is
`W2MkkArbitraryExit.firstOrientationDictionary`'s output and `memberGenus` is
`firstOrientationSourceGenus`'s; both are supplied below from the branch swap
alone. -/
noncomputable def mkkFirstFullDim
    (dictionary : ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus).member position).datum)
    (memberGenus : ∀ position : Fin 3,
      genus ((W2MkkLimitColumns.firstOrientation input shape member distinguished
        hConnected hGenus).member position).datum.sourceGraph = genus data.sourceGraph) :
    ∀ outgoing : Fin 3,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((mkkFirstFamily input shape member distinguished hConnected hGenus incoming
          incomingFD).presentation outgoing)).det ≠ 0 →
      FullDimensionalSourcePresentation
        ((mkkFirstFamily input shape member distinguished hConnected hGenus incoming
          incomingFD).candidate outgoing).datum coordinate
  | 0 => fun hdet ↦ W2MkkStableIncidence.presentationAt
      (W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus) incoming 0 ((dictionary incoming).symm.trans (dictionary 0))
      input.valid hConnected hGenus (memberGenus incoming) (memberGenus 0)
      (W2MkkArbitraryExit.initialLabelling _ incoming incomingFD) incomingFD hdet
  | 1 => fun hdet ↦ W2MkkStableIncidence.presentationAt
      (W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus) incoming 1 ((dictionary incoming).symm.trans (dictionary 1))
      input.valid hConnected hGenus (memberGenus incoming) (memberGenus 1)
      (W2MkkArbitraryExit.initialLabelling _ incoming incomingFD) incomingFD hdet
  | 2 => fun hdet ↦ W2MkkStableIncidence.presentationAt
      (W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus) incoming 2 ((dictionary incoming).symm.trans (dictionary 2))
      input.valid hConnected hGenus (memberGenus incoming) (memberGenus 2)
      (W2MkkArbitraryExit.initialLabelling _ incoming incomingFD) incomingFD hdet

/-- **The full-dimensional supply for `w2Mkk`, Base II.2.1.M.** -/
noncomputable def w2MkkFirstSupply
    (dictionary : ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus).member position).datum)
    (memberGenus : ∀ position : Fin 3,
      genus ((W2MkkLimitColumns.firstOrientation input shape member distinguished
        hConnected hGenus).member position).datum.sourceGraph = genus data.sourceGraph)
    (hwallColumn : (mkkFirstFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2MkkFirst (wall := wall) input shape member distinguished
      hConnected hGenus incoming incomingFD hwallColumn root) where
  fullDim := mkkFirstFullDim input shape member distinguished hConnected hGenus incoming
    incomingFD dictionary memberGenus
  presentation_eq := by
    intro outgoing hdet
    fin_cases outgoing <;> rfl

/-! ### The two remaining fields, discharged from the branch swap alone

`W2MkkArbitraryExit.RemoteDictionary` is `Nonempty (StableGraphIncidence.Equivalence
data (W2MkkTransport.swapRelabeling …).apply)` -- a statement about an arbitrary
compatible global sheet relabelling, with no case data in it.
`StableGraphIncidence.sheetRelabel` is that equivalence, and
`GluingDatum.SheetRelabeling.sourceGraphLaplacianEquiv` is the matching genus
receipt.  The module `SheetRelabelIncidence` states the two under its own names;
here the two lines below are the whole of it, and `mkkFirstSupply` carries no
condition. -/

/-- The three Base II.2.1.M dictionaries, the remote one included. -/
noncomputable def mkkFirstDictionary :
    ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus).member position).datum :=
  W2MkkArbitraryExit.firstOrientationDictionary input shape distinguished hConnected
    hGenus member
    (StableGraphIncidence.sheetRelabel
      (W2MkkTransport.swapRelabeling profile (secondSheet profile)
        (W2MkkTransport.secondSheet_together profile)) input.valid.1)

/-- and the three source-genus receipts. -/
theorem mkkFirstMemberGenus : ∀ position : Fin 3,
    genus ((W2MkkLimitColumns.firstOrientation input shape member distinguished
      hConnected hGenus).member position).datum.sourceGraph = genus data.sourceGraph :=
  W2MkkArbitraryExit.firstOrientationSourceGenus input shape distinguished hConnected
    hGenus member
    (W2MkkTransport.swapRelabeling profile (secondSheet profile)
      (W2MkkTransport.secondSheet_together profile)).sourceGraphLaplacianEquiv.genus_eq

/-- **The full-dimensional supply for `w2Mkk`, Base II.2.1.M, with nothing
carried.** -/
noncomputable def mkkFirstSupply
    (hwallColumn : (mkkFirstFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2MkkFirst (wall := wall) input shape member distinguished
      hConnected hGenus incoming incomingFD hwallColumn root) :=
  w2MkkFirstSupply input shape member distinguished hConnected hGenus incoming incomingFD
    (mkkFirstDictionary input shape member distinguished hConnected hGenus)
    (mkkFirstMemberGenus input shape member distinguished hConnected hGenus)
    hwallColumn root

/-! ### The incoming side -/

/-- The family's presented matrices are the orientation's own square matrices. -/
theorem ofW2MkkFirst_presentation_matrix
    (hwallColumn : (mkkFirstFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2MkkFirst (wall := wall) input shape member distinguished hConnected hGenus
          incoming incomingFD hwallColumn root).family.presentation i) =
      (W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus).squareMatrix
        (W2MkkArbitraryExit.initialLabelling
          (W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
            hGenus) incoming incomingFD) i :=
  W2MkkArbitraryExit.firstPresentation_matrix input shape distinguished hConnected hGenus
    member
    (W2MkkArbitraryExit.initialLabelling
      (W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
        hGenus) incoming incomingFD) i

/-- **`hW25IncomingNonzero` for `w2Mkk`, Base II.2.1.M.**
`W2MkkArbitraryExit.squareMatrix_self_ne_zero`. -/
theorem ofW2MkkFirst_incomingNonzero
    (hwallColumn : (mkkFirstFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((ofW2MkkFirst (wall := wall) input shape member distinguished hConnected hGenus
        incoming incomingFD hwallColumn root).family.presentation incoming)).det ≠ 0 := by
  rw [ofW2MkkFirst_presentation_matrix input shape member distinguished hConnected hGenus
    incoming incomingFD hwallColumn root]
  exact W2MkkArbitraryExit.squareMatrix_self_ne_zero _ incoming incomingFD

/-- **`hW25IncomingMatrix` for `w2Mkk`, Base II.2.1.M, modulo the state–classifier
equation.**  `hChart` is the single named hypothesis; the rest is
`W2MkkArbitraryExit.squareMatrix_self`. -/
theorem ofW2MkkFirst_incomingMatrix
    (hwallColumn : (mkkFirstFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2MkkFirst (wall := wall) input shape member distinguished hConnected hGenus
          incoming incomingFD hwallColumn root).family.presentation incoming) = chart := by
  rw [ofW2MkkFirst_presentation_matrix input shape member distinguished hConnected hGenus
    incoming incomingFD hwallColumn root, W2MkkArbitraryExit.squareMatrix_self]
  exact hChart

/-- **`hW25Nodup` for `w2Mkk`, Base II.2.1.M.** -/
theorem ofW2MkkFirst_nodup
    (hwallColumn : (mkkFirstFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) (row : coordinate) :
    (((ofW2MkkFirst (wall := wall) input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root).family.presentation i).path row).Nodup := by
  fin_cases i <;> exact nodup_labelling_path _ row

/-- The Base II.2.1.M family is honestly presented. -/
theorem ofW2MkkFirst_honestlyPresented
    (hwallColumn : (mkkFirstFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (ofW2MkkFirst (wall := wall) input shape member
      distinguished hConnected hGenus incoming incomingFD hwallColumn root) := by
  intro i
  fin_cases i <;> exact ⟨_, rfl⟩

/-- **`w2Mkk` as a routed wall, Base II.2.1.M.**  Nothing is carried but
`hChart`. -/
noncomputable def routedW2MkkFirst
    (hwallColumn : (mkkFirstFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply
    (ofW2MkkFirst (wall := wall) input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root)
    (mkkFirstSupply input shape member distinguished hConnected hGenus incoming incomingFD
      hwallColumn root)
    (ofW2MkkFirst_honestlyPresented input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root)
    incoming
    (ofW2MkkFirst_incomingNonzero input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root)
    (ofW2MkkFirst_incomingMatrix input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root chart hChart)

/-- The Base II.2.1.M family's regrown column, read on the identified member's
own occurrence dictionary (`W2MkkArbitraryExit.wallColumn_initialLabelling`). -/
theorem mkkFirstFamily_wallColumn :
    (mkkFirstFamily input shape member distinguished hConnected hGenus incoming
        incomingFD).wallColumn =
      incomingFD.labelling.targetEdge.symm
        (occurrenceEquiv target wallVertex
          ((W2MkkLimitColumns.firstOrientation input shape member distinguished hConnected
            hGenus).member incoming).right none) :=
  W2MkkArbitraryExit.wallColumn_initialLabelling _ incoming incomingFD

end W2MkkFirst

/-! ## 4.  `w2Mkk`, Base II.2.2.M -/

section W2MkkSecond

open W2MkkSourceCandidates

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wallVertex}
  {block : WallBlock data wallVertex}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  (input : W2SourceInput data star) (shape : Shape profile)
  (member : SecondMember profile) (distinguished : Fin degree)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
      hGenus).member incoming).datum coordinate)

/-- Figure 34's honest family in the identified member's own square
coordinates, Base II.2.2.M. -/
noncomputable def mkkSecondFamily :
    GaugeFamily (coordinate := coordinate) 3 data wallVertex :=
  W2MkkArbitraryExit.secondGaugeFamily input shape distinguished hConnected hGenus member
    (W2MkkArbitraryExit.initialLabelling
      (W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus) incoming incomingFD)

/-- **Figure 34's wall input, Base II.2.2.M.**  Gauge-mixed: position `0` lives
over the branch-swapped copy, which is exactly what `WallInput.ofGauge` exists
for. -/
noncomputable def ofW2MkkSecond
    (hwallColumn : (mkkSecondFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    WallInput degree coordinate wall :=
  WallInput.ofGauge (mkkSecondFamily input shape member distinguished hConnected hGenus
    incoming incomingFD) input.valid SourceCase.w2Mkk rfl hwallColumn hConnected hGenus
    root

@[simp] theorem ofW2MkkSecond_case
    (hwallColumn : (mkkSecondFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (ofW2MkkSecond (wall := wall) input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root).case = SourceCase.w2Mkk := rfl

/-- Figure 34's three outgoing presentations in the Base II.2.2.M orientation,
one `W2MkkStableIncidence.presentationAt` per member.  `dictionary` is
`W2MkkArbitraryExit.secondOrientationDictionary`'s output and `memberGenus` is
`secondOrientationSourceGenus`'s; both are supplied below from the branch swap
alone. -/
noncomputable def mkkSecondFullDim
    (dictionary : ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus).member position).datum)
    (memberGenus : ∀ position : Fin 3,
      genus ((W2MkkLimitColumns.secondOrientation input shape member distinguished
        hConnected hGenus).member position).datum.sourceGraph = genus data.sourceGraph) :
    ∀ outgoing : Fin 3,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((mkkSecondFamily input shape member distinguished hConnected hGenus incoming
          incomingFD).presentation outgoing)).det ≠ 0 →
      FullDimensionalSourcePresentation
        ((mkkSecondFamily input shape member distinguished hConnected hGenus incoming
          incomingFD).candidate outgoing).datum coordinate
  | 0 => fun hdet ↦ W2MkkStableIncidence.presentationAt
      (W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus) incoming 0 ((dictionary incoming).symm.trans (dictionary 0))
      input.valid hConnected hGenus (memberGenus incoming) (memberGenus 0)
      (W2MkkArbitraryExit.initialLabelling _ incoming incomingFD) incomingFD hdet
  | 1 => fun hdet ↦ W2MkkStableIncidence.presentationAt
      (W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus) incoming 1 ((dictionary incoming).symm.trans (dictionary 1))
      input.valid hConnected hGenus (memberGenus incoming) (memberGenus 1)
      (W2MkkArbitraryExit.initialLabelling _ incoming incomingFD) incomingFD hdet
  | 2 => fun hdet ↦ W2MkkStableIncidence.presentationAt
      (W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus) incoming 2 ((dictionary incoming).symm.trans (dictionary 2))
      input.valid hConnected hGenus (memberGenus incoming) (memberGenus 2)
      (W2MkkArbitraryExit.initialLabelling _ incoming incomingFD) incomingFD hdet

/-- **The full-dimensional supply for `w2Mkk`, Base II.2.2.M.** -/
noncomputable def w2MkkSecondSupply
    (dictionary : ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus).member position).datum)
    (memberGenus : ∀ position : Fin 3,
      genus ((W2MkkLimitColumns.secondOrientation input shape member distinguished
        hConnected hGenus).member position).datum.sourceGraph = genus data.sourceGraph)
    (hwallColumn : (mkkSecondFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2MkkSecond (wall := wall) input shape member distinguished
      hConnected hGenus incoming incomingFD hwallColumn root) where
  fullDim := mkkSecondFullDim input shape member distinguished hConnected hGenus incoming
    incomingFD dictionary memberGenus
  presentation_eq := by
    intro outgoing hdet
    fin_cases outgoing <;> rfl

/-! ### The two remaining fields, discharged from the branch swap alone

`W2MkkArbitraryExit.RemoteDictionary` is `Nonempty (StableGraphIncidence.Equivalence
data (W2MkkTransport.swapRelabeling …).apply)` -- a statement about an arbitrary
compatible global sheet relabelling, with no case data in it.
`StableGraphIncidence.sheetRelabel` is that equivalence, and
`GluingDatum.SheetRelabeling.sourceGraphLaplacianEquiv` is the matching genus
receipt.  The module `SheetRelabelIncidence` states the two under its own names;
here the two lines below are the whole of it, and `mkkSecondSupply` carries no
condition. -/

/-- The three Base II.2.2.M dictionaries, the remote one included. -/
noncomputable def mkkSecondDictionary :
    ∀ position : Fin 3, StableGraphIncidence.Equivalence data
      ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus).member position).datum :=
  W2MkkArbitraryExit.secondOrientationDictionary input shape distinguished hConnected
    hGenus member
    (StableGraphIncidence.sheetRelabel
      (W2MkkTransport.swapRelabeling profile (firstSheet profile)
        (W2MkkTransport.firstSheet_together profile)) input.valid.1)

/-- and the three source-genus receipts. -/
theorem mkkSecondMemberGenus : ∀ position : Fin 3,
    genus ((W2MkkLimitColumns.secondOrientation input shape member distinguished
      hConnected hGenus).member position).datum.sourceGraph = genus data.sourceGraph :=
  W2MkkArbitraryExit.secondOrientationSourceGenus input shape distinguished hConnected
    hGenus member
    (W2MkkTransport.swapRelabeling profile (firstSheet profile)
      (W2MkkTransport.firstSheet_together profile)).sourceGraphLaplacianEquiv.genus_eq

/-- **The full-dimensional supply for `w2Mkk`, Base II.2.2.M, with nothing
carried.** -/
noncomputable def mkkSecondSupply
    (hwallColumn : (mkkSecondFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    FullDimSupply (ofW2MkkSecond (wall := wall) input shape member distinguished
      hConnected hGenus incoming incomingFD hwallColumn root) :=
  w2MkkSecondSupply input shape member distinguished hConnected hGenus incoming incomingFD
    (mkkSecondDictionary input shape member distinguished hConnected hGenus)
    (mkkSecondMemberGenus input shape member distinguished hConnected hGenus)
    hwallColumn root

/-! ### The incoming side -/

/-- The family's presented matrices are the orientation's own square matrices. -/
theorem ofW2MkkSecond_presentation_matrix
    (hwallColumn : (mkkSecondFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2MkkSecond (wall := wall) input shape member distinguished hConnected hGenus
          incoming incomingFD hwallColumn root).family.presentation i) =
      (W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus).squareMatrix
        (W2MkkArbitraryExit.initialLabelling
          (W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
            hGenus) incoming incomingFD) i :=
  W2MkkArbitraryExit.secondPresentation_matrix input shape distinguished hConnected hGenus
    member
    (W2MkkArbitraryExit.initialLabelling
      (W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
        hGenus) incoming incomingFD) i

/-- **`hW25IncomingNonzero` for `w2Mkk`, Base II.2.2.M.**
`W2MkkArbitraryExit.squareMatrix_self_ne_zero`. -/
theorem ofW2MkkSecond_incomingNonzero
    (hwallColumn : (mkkSecondFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((ofW2MkkSecond (wall := wall) input shape member distinguished hConnected hGenus
        incoming incomingFD hwallColumn root).family.presentation incoming)).det ≠ 0 := by
  rw [ofW2MkkSecond_presentation_matrix input shape member distinguished hConnected hGenus
    incoming incomingFD hwallColumn root]
  exact W2MkkArbitraryExit.squareMatrix_self_ne_zero _ incoming incomingFD

/-- **`hW25IncomingMatrix` for `w2Mkk`, Base II.2.2.M, modulo the state–classifier
equation.**  `hChart` is the single named hypothesis; the rest is
`W2MkkArbitraryExit.squareMatrix_self`. -/
theorem ofW2MkkSecond_incomingMatrix
    (hwallColumn : (mkkSecondFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofW2MkkSecond (wall := wall) input shape member distinguished hConnected hGenus
          incoming incomingFD hwallColumn root).family.presentation incoming) = chart := by
  rw [ofW2MkkSecond_presentation_matrix input shape member distinguished hConnected hGenus
    incoming incomingFD hwallColumn root, W2MkkArbitraryExit.squareMatrix_self]
  exact hChart

/-- **`hW25Nodup` for `w2Mkk`, Base II.2.2.M.** -/
theorem ofW2MkkSecond_nodup
    (hwallColumn : (mkkSecondFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) (i : Fin 3) (row : coordinate) :
    (((ofW2MkkSecond (wall := wall) input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root).family.presentation i).path row).Nodup := by
  fin_cases i <;> exact nodup_labelling_path _ row

/-- The Base II.2.2.M family is honestly presented. -/
theorem ofW2MkkSecond_honestlyPresented
    (hwallColumn : (mkkSecondFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (ofW2MkkSecond (wall := wall) input shape member
      distinguished hConnected hGenus incoming incomingFD hwallColumn root) := by
  intro i
  fin_cases i <;> exact ⟨_, rfl⟩

/-- **`w2Mkk` as a routed wall, Base II.2.2.M.**  Nothing is carried but
`hChart`. -/
noncomputable def routedW2MkkSecond
    (hwallColumn : (mkkSecondFamily input shape member distinguished hConnected hGenus
      incoming incomingFD).wallColumn = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (hChart : GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation incomingFD.labelling) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply
    (ofW2MkkSecond (wall := wall) input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root)
    (mkkSecondSupply input shape member distinguished hConnected hGenus incoming incomingFD
      hwallColumn root)
    (ofW2MkkSecond_honestlyPresented input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root)
    incoming
    (ofW2MkkSecond_incomingNonzero input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root)
    (ofW2MkkSecond_incomingMatrix input shape member distinguished hConnected hGenus
      incoming incomingFD hwallColumn root chart hChart)

/-- The Base II.2.2.M family's regrown column, read on the identified member's
own occurrence dictionary (`W2MkkArbitraryExit.wallColumn_initialLabelling`). -/
theorem mkkSecondFamily_wallColumn :
    (mkkSecondFamily input shape member distinguished hConnected hGenus incoming
        incomingFD).wallColumn =
      incomingFD.labelling.targetEdge.symm
        (occurrenceEquiv target wallVertex
          ((W2MkkLimitColumns.secondOrientation input shape member distinguished hConnected
            hGenus).member incoming).right none) :=
  W2MkkArbitraryExit.wallColumn_initialLabelling _ incoming incomingFD

end W2MkkSecond



/-! ## 5.  `w3Four`

`W3WallInput.ofFour` already routes this tag, but its family carries
`Figure28Receipts.presentation`, and those are identified with the honest ones
only as **matrices** (`W3FourRegrownColumn.IsHonest`), not as
`LengthMatrixPresentation`s.  The supply's `presentation_eq` needs the latter, so
the wall input here is built from the members' own honest labellings
(`W3FourHonestBalance.HonestFigure28.labelling`) instead: same members, same
gauge copies, same tag, same determinants -- `figure28HonestFamily_det` -- and
`presentation_eq` becomes `rfl`.

**The two carried fields.**  `W3FourStableIncidence.HonestFigure28Exit.presentationAt`
takes the member-to-member dictionary and the two source-genus receipts as
hypotheses, because `W3FourStableGraph.MemberColumn` carries no genus field; so
`figure28FullDim`, `w3FourSupply` and `routedW3Four` carry

```
certificate : ∀ i j, StableGraphIncidence.Equivalence
  (honestReceipts.candidate i).datum (honestReceipts.candidate j).datum
memberGenus : ∀ i, genus (honestReceipts.candidate i).datum.sourceGraph = genus data.sourceGraph
```

verbatim as `HonestFigure28Exit.exists_valid_positive_exit_presentation` does.
`W3FourStableIncidence.exists_figure28Dictionaries` builds four
`MemberDictionary`s carrying exactly these two fields, on exactly the hypotheses
`W3FourRegrownColumn.exists_figure28Receipts_honest` takes -- but over *its own*
`W3FourClosure.exists_member_one`/`exists_member_two` choices, and
`exists_figure28Receipts_honest` existentially quantifies its receipts without
exposing the `positionOne`/`positionTwo`/`permOne`/`permTwo` it built them from.
So the two cannot be composed directly.  What composes them is one extended
existential: the honest receipts returned together with the four
`MemberDictionary`s at the same members (its `cdOne`, `cdTwo`, `cdThree`,
`cdFour` are `positionOneColumnData`, `positionTwoColumnData` and two
`growColumnData`s, whose `memberColumn.candidate`s are literally
`positionOne.candidate`, `positionTwo.candidate` and the two `growCandidate`s).
That existential is `W3FourRegrownColumnSeam.exists_memberCertificates`, and
`TrackedWallProgressMore.routedW3FourHonest` uses it to supply `routedW3Four`'s
two arguments. -/

section W3Four

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree}
  {geometry : W3FourClosure.FourStarGeometry data wallVertex}
  (honestReceipts : W3FourHonestBalance.HonestFigure28 data wallVertex geometry)
  (relabel : coordinate ≃ Option target.edges)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- Figure 28's four honest labellings, moved to the ambient coordinate. -/
noncomputable def figure28Labelling (i : Fin 4) :
    StableLengthMatrixLabelling (honestReceipts.candidate i).datum coordinate :=
  reindexLabelling relabel (honestReceipts.labelling i)

omit [Fintype coordinate] in
theorem figure28Labelling_matrix (i : Fin 4) :
    GluingDatum.LengthMatrixPresentation.matrix
        (StableLengthMatrixLabelling.presentation
          (figure28Labelling honestReceipts relabel i)) =
      GluingDatum.LengthMatrixPresentation.matrix
        (ClassifierInterface.reindex relabel (honestReceipts.gaugeFamily.presentation i)) := by
  rw [figure28Labelling, reindexLabelling_matrix, ClassifierInterface.matrix_reindex,
    honestReceipts.labelling_matrix i]

/-- **Equation (2)'s honest gauge family at the march's coordinate.**  The four
members, the four gauge copies and the four Figure 28 determinants are
`W3FourHonestBalance.HonestFigure28.gaugeFamily`'s, unchanged; only the
presentations are replaced by the members' own honest labellings, which by
`HonestFigure28.labelling_matrix` have the very same matrices.  So
`positiveBalance` and `agreeOffWall` are the reindexed family's, rewritten
along that identity, and nothing is assumed. -/
noncomputable def figure28HonestFamily :
    GaugeFamily (coordinate := coordinate) 4 data wallVertex where
  base := honestReceipts.base
  valid_of_old := honestReceipts.gaugeFamily.valid_of_old
  candidate := honestReceipts.candidate
  presentation := fun i ↦ StableLengthMatrixLabelling.presentation
    (figure28Labelling honestReceipts relabel i)
  wallColumn := relabel.symm none
  weight := honestReceipts.gaugeFamily.weight
  positiveBalance := by
    refine ⟨(gaugeFamilyReindex relabel honestReceipts.gaugeFamily).positiveBalance.1, ?_⟩
    have h : ∑ i, honestReceipts.gaugeFamily.weight i *
        (GluingDatum.LengthMatrixPresentation.matrix (ClassifierInterface.reindex relabel
          (honestReceipts.gaugeFamily.presentation i))).det = 0 :=
      (gaugeFamilyReindex relabel honestReceipts.gaugeFamily).positiveBalance.2
    simpa only [figure28Labelling_matrix honestReceipts relabel] using h
  agreeOffWall := fun first second ↦ by
    rw [figure28Labelling_matrix honestReceipts relabel first,
      figure28Labelling_matrix honestReceipts relabel second]
    exact (gaugeFamilyReindex relabel honestReceipts.gaugeFamily).agreeOffWall first second

@[simp] theorem figure28HonestFamily_candidate (i : Fin 4) :
    (figure28HonestFamily honestReceipts relabel).candidate i =
      honestReceipts.candidate i := rfl

@[simp] theorem figure28HonestFamily_base (i : Fin 4) :
    (figure28HonestFamily honestReceipts relabel).base i =
      honestReceipts.base i := rfl

/-- Its determinants are Figure 28's own. -/
theorem figure28HonestFamily_det (i : Fin 4) :
    (GluingDatum.LengthMatrixPresentation.matrix
        ((figure28HonestFamily honestReceipts relabel).presentation
          i)).det =
      (GluingDatum.LengthMatrixPresentation.matrix
        (honestReceipts.gaugeFamily.presentation i)).det := by
  show (GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation
        (figure28Labelling honestReceipts relabel i))).det = _
  rw [figure28Labelling_matrix honestReceipts relabel i,
    ClassifierInterface.det_matrix_reindex]

/-- **Equation (2)'s wall input on the honest matrices.**  `W3WallInput.ofFour`'s
sibling: same members, same bases, same tag, same determinants -- the family
differs only in carrying the members' own honest presentations, which is exactly
what the supply's `presentation_eq` needs and what `receipts.presentation` cannot
give. -/
noncomputable def ofFourHonest (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (hrelabel : relabel wall = none) :
    WallInput degree coordinate wall :=
  WallInput.ofGauge (figure28HonestFamily honestReceipts relabel)
    hValid SourceCase.w3Four rfl
    ((Equiv.symm_apply_eq relabel).mpr hrelabel.symm) targetConnected targetGenus root

@[simp] theorem ofFourHonest_case (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (hrelabel : relabel wall = none) :
    (ofFourHonest (wall := wall) honestReceipts relabel hValid targetConnected targetGenus
      root hrelabel).case = SourceCase.w3Four := rfl

@[simp] theorem ofFourHonest_data (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (hrelabel : relabel wall = none) :
    (ofFourHonest (wall := wall) honestReceipts relabel hValid targetConnected targetGenus
      root hrelabel).data = data := rfl

/-- Figure 28's four outgoing presentations, one
`W3FourStableIncidence.HonestFigure28Exit.presentationAt` per member, moved to
the ambient coordinate.  `certificate` and `memberGenus` are the two carried fields;
see the section note. -/
noncomputable def figure28FullDim
    (certificate : ∀ i j, StableGraphIncidence.Equivalence
      (honestReceipts.candidate i).datum (honestReceipts.candidate j).datum)
    (memberGenus : ∀ i,
      genus (honestReceipts.candidate i).datum.sourceGraph = genus data.sourceGraph)
    (hValid : data.Valid) (targetConnected : graph_connected target)
    (targetGenus : genus target = 0) (incoming : Fin 4)
    (incomingFD : FullDimensionalSourcePresentation
      (honestReceipts.candidate incoming).datum (Option target.edges)) :
    ∀ outgoing : Fin 4,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((figure28HonestFamily honestReceipts
          relabel).presentation outgoing)).det ≠ 0 →
      FullDimensionalSourcePresentation
        ((figure28HonestFamily honestReceipts
          relabel).candidate outgoing).datum coordinate :=
  fun outgoing hdet ↦ reindexFullDim relabel
    (W3FourStableIncidence.HonestFigure28Exit.presentationAt honestReceipts incoming outgoing
      (certificate incoming outgoing) hValid targetConnected targetGenus
      (memberGenus incoming) (memberGenus outgoing) incomingFD
      (by
        rw [← figure28HonestFamily_det honestReceipts relabel outgoing]
        exact hdet))

/-- **The full-dimensional supply for `w3Four`.**  `presentation_eq` is `rfl`:
the family carries the honest labellings that `HonestFigure28Exit.presentationAt`
installs, moved by the same `relabel`. -/
noncomputable def w3FourSupply
    (certificate : ∀ i j, StableGraphIncidence.Equivalence
      (honestReceipts.candidate i).datum (honestReceipts.candidate j).datum)
    (memberGenus : ∀ i,
      genus (honestReceipts.candidate i).datum.sourceGraph = genus data.sourceGraph)
    (hValid : data.Valid) (targetConnected : graph_connected target)
    (targetGenus : genus target = 0) (incoming : Fin 4)
    (incomingFD : FullDimensionalSourcePresentation
      (honestReceipts.candidate incoming).datum (Option target.edges))
    (root : target.V) (hrelabel : relabel wall = none) :
    FullDimSupply (ofFourHonest (wall := wall) honestReceipts relabel hValid
      targetConnected targetGenus root hrelabel) where
  fullDim := figure28FullDim honestReceipts relabel certificate
    memberGenus hValid targetConnected targetGenus incoming incomingFD
  presentation_eq := fun _ _ ↦ rfl

/-! ### The incoming side -/

/-- **`hW25IncomingNonzero` for `w3Four`.**  Equation (2)'s determinant at the
identified position is the incoming member's own, by
`HonestFigure28.labelling_matrix`. -/
theorem ofFourHonest_incomingNonzero (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (hrelabel : relabel wall = none) (incoming : Fin 4)
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.gaugeFamily.presentation incoming)).det ≠ 0) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((ofFourHonest (wall := wall) honestReceipts relabel hValid targetConnected
        targetGenus root hrelabel).family.presentation incoming)).det ≠ 0 := by
  show (GluingDatum.LengthMatrixPresentation.matrix
      ((figure28HonestFamily honestReceipts
        relabel).presentation incoming)).det ≠ 0
  rw [figure28HonestFamily_det honestReceipts relabel incoming]
  exact hincoming

/-- **`hW25IncomingMatrix` for `w3Four`, modulo the state–classifier equation.**
`hChart` is the single named hypothesis: the chart the march occupies is
Equation (2)'s matrix at the identified position, read in the ambient
coordinate. -/
theorem ofFourHonest_incomingMatrix (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (hrelabel : relabel wall = none) (incoming : Fin 4)
    (chart : Matrix coordinate coordinate ℚ)
    (hChart : (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.gaugeFamily.presentation incoming)).submatrix relabel relabel =
        chart) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((ofFourHonest (wall := wall) honestReceipts relabel hValid targetConnected
          targetGenus root hrelabel).family.presentation incoming) = chart := by
  show GluingDatum.LengthMatrixPresentation.matrix
      (StableLengthMatrixLabelling.presentation
        (figure28Labelling honestReceipts relabel incoming)) =
    chart
  rw [figure28Labelling_matrix honestReceipts relabel incoming,
    ClassifierInterface.matrix_reindex]
  exact hChart

/-- **`hW25Nodup` for `w3Four`.** -/
theorem ofFourHonest_nodup (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (hrelabel : relabel wall = none) (i : Fin 4) (row : coordinate) :
    (((ofFourHonest (wall := wall) honestReceipts relabel hValid targetConnected
      targetGenus root hrelabel).family.presentation i).path row).Nodup :=
  nodup_labelling_path
    (figure28Labelling honestReceipts relabel i) row

/-- The honest Equation (2) family is honestly presented. -/
theorem ofFourHonest_honestlyPresented (hValid : data.Valid)
    (targetConnected : graph_connected target) (targetGenus : genus target = 0)
    (root : target.V) (hrelabel : relabel wall = none) :
    RoutedWall.HonestlyPresented (ofFourHonest (wall := wall) honestReceipts relabel
      hValid targetConnected targetGenus root hrelabel) :=
  fun i ↦ ⟨figure28Labelling honestReceipts relabel i, rfl⟩

/-- **`w3Four` as a routed wall.**  `certificate` and `memberGenus` are carried;
see the section note for what discharges them. -/
noncomputable def routedW3Four
    (certificate : ∀ i j, StableGraphIncidence.Equivalence
      (honestReceipts.candidate i).datum (honestReceipts.candidate j).datum)
    (memberGenus : ∀ i,
      genus (honestReceipts.candidate i).datum.sourceGraph = genus data.sourceGraph)
    (hValid : data.Valid) (targetConnected : graph_connected target)
    (targetGenus : genus target = 0) (incoming : Fin 4)
    (incomingFD : FullDimensionalSourcePresentation
      (honestReceipts.candidate incoming).datum (Option target.edges))
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.gaugeFamily.presentation incoming)).det ≠ 0)
    (root : target.V) (hrelabel : relabel wall = none)
    (chart : Matrix coordinate coordinate ℚ)
    (hChart : (GluingDatum.LengthMatrixPresentation.matrix
      (honestReceipts.gaugeFamily.presentation incoming)).submatrix relabel relabel =
        chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply
    (ofFourHonest (wall := wall) honestReceipts relabel hValid targetConnected targetGenus
      root hrelabel)
    (w3FourSupply honestReceipts relabel certificate memberGenus hValid targetConnected
      targetGenus incoming incomingFD root hrelabel)
    (ofFourHonest_honestlyPresented honestReceipts relabel hValid targetConnected
      targetGenus root hrelabel)
    incoming
    (ofFourHonest_incomingNonzero honestReceipts relabel hValid targetConnected targetGenus
      root hrelabel incoming hincoming)
    (ofFourHonest_incomingMatrix honestReceipts relabel hValid targetConnected targetGenus
      root hrelabel incoming chart hChart)

end W3Four


/-! ## 6.  The three tags `A04FourTags` already supplies, as routed walls -/

section AlreadySupplied

open ThirdEquation
open W3R1SourceProfile
open W4TargetPairings

variable {target : CFGraph.{0}} {wallVertex : target.V}
  {data : GluingDatum target degree}

section Nd2

variable {star : ThreeStar target wallVertex}
  (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate)

/-- Equation (5)'s family is honestly presented. -/
theorem ofNd2CoarseFine_honestlyPresented
    (hwallColumn : W3Nd2CommonBalance.wallColumn input profile
      (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD) = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (W3WallInput.ofNd2CoarseFine (wall := wall) input profile
      (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD) hwallColumn
      hConnected hGenus root) := by
  intro i
  fin_cases i <;> exact ⟨_, rfl⟩

/-- **`w3Nd2CoarseFine` as a routed wall.**  `A04FourTags.nd2Supply` is the pair;
the incoming triple is carried, because Equation (5)'s incoming side is proved
with the `w3Nd2CoarseFine` case itself, not here. -/
noncomputable def routedNd2
    (hwallColumn : W3Nd2CommonBalance.wallColumn input profile
      (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD) = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (position : Fin 2)
    (hNonzero : (GluingDatum.LengthMatrixPresentation.matrix
      ((W3WallInput.ofNd2CoarseFine (wall := wall) input profile
        (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD)
        hwallColumn hConnected hGenus root).family.presentation position)).det ≠ 0)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix
      ((W3WallInput.ofNd2CoarseFine (wall := wall) input profile
        (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD)
        hwallColumn hConnected hGenus root).family.presentation position) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply _
    (A04FourTags.nd2Supply input profile hConnected hGenus incoming incomingFD hwallColumn
      root)
    (ofNd2CoarseFine_honestlyPresented input profile hConnected hGenus incoming incomingFD
      hwallColumn root)
    position hNonzero hMatrix

end Nd2

section Nd3

variable {star : ThreeStar target wallVertex}
  (input : W3SourceInput data star)
  (profile : Nd3Profile data input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd3CommonBalance.candidates input profile hSame incoming).datum coordinate)

/-- Equation (4)'s family is honestly presented. -/
theorem ofNd3CoarseFine_honestlyPresented
    (hwallColumn : W3Nd3CommonBalance.wallColumn input profile hSame
      (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD) = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (W3WallInput.ofNd3CoarseFine (wall := wall) input profile
      hSame (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD)
      hwallColumn hConnected hGenus root) :=
  fun _ ↦ ⟨_, rfl⟩

/-- **`w3Nd3CoarseFine` as a routed wall.** -/
noncomputable def routedNd3
    (hwallColumn : W3Nd3CommonBalance.wallColumn input profile hSame
      (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD) = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (position : Fin 2)
    (hNonzero : (GluingDatum.LengthMatrixPresentation.matrix
      ((W3WallInput.ofNd3CoarseFine (wall := wall) input profile hSame
        (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD)
        hwallColumn hConnected hGenus root).family.presentation position)).det ≠ 0)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix
      ((W3WallInput.ofNd3CoarseFine (wall := wall) input profile hSame
        (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD)
        hwallColumn hConnected hGenus root).family.presentation position) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply _
    (A04FourTags.nd3Supply input profile hSame hConnected hGenus incoming incomingFD
      hwallColumn root)
    (ofNd3CoarseFine_honestlyPresented input profile hSame hConnected hGenus incoming
      incomingFD hwallColumn root)
    position hNonzero hMatrix

end Nd3

section W4

variable [DecidableEq target.edges] {star : FourStar target wallVertex}
  (source : W4StableSource.AuxR0SourceInput data star)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    (W4OutgoingStableRows.member source incoming).datum coordinate)

/-- Equation (1)'s honest family is honestly presented. -/
theorem ofFourValentHonest_honestlyPresented
    (hwallColumn : W4PositiveExit.wallColumn source incoming incomingFD = wall)
    (root : target.V) :
    RoutedWall.HonestlyPresented (A04FourTags.ofFourValentHonest (wall := wall) source
      hConnected hGenus incoming incomingFD hwallColumn root) :=
  fun _ ↦ ⟨_, rfl⟩

/-- **`w4` as a routed wall.** -/
noncomputable def routedW4
    (hwallColumn : W4PositiveExit.wallColumn source incoming incomingFD = wall)
    (root : target.V) (chart : Matrix coordinate coordinate ℚ)
    (position : Fin 3)
    (hNonzero : (GluingDatum.LengthMatrixPresentation.matrix
      ((A04FourTags.ofFourValentHonest (wall := wall) source hConnected hGenus incoming
        incomingFD hwallColumn root).family.presentation position)).det ≠ 0)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix
      ((A04FourTags.ofFourValentHonest (wall := wall) source hConnected hGenus incoming
        incomingFD hwallColumn root).family.presentation position) = chart) :
    RoutedWall degree coordinate chart wall :=
  RoutedWall.ofHonestSupply _
    (A04FourTags.w4Supply source hConnected hGenus incoming incomingFD hwallColumn root)
    (ofFourValentHonest_honestlyPresented source hConnected hGenus incoming incomingFD
      hwallColumn root)
    position hNonzero hMatrix

end W4

end AlreadySupplied


/-! ## 7.  The seven routed-and-supplied tags (all ten with `A04M11Wiring`, `A04M1kWiring`, `A04ShiftWiring`, `A04R1Wiring`)

`RoutedWall` is inhabited at a coordinate by any one of

| tag | constructor | supply |
|---|---|---|
| `w2P` | `routedW2P` | `w2PSupply` |
| `w2Mkk` (Base II.2.1.M) | `routedW2MkkFirst` | `mkkFirstSupply` |
| `w2Mkk` (Base II.2.2.M) | `routedW2MkkSecond` | `mkkSecondSupply` |
| `w3Four` | `routedW3Four` | `w3FourSupply` |
| `w2M11` (in `A04M11Wiring`) | `A04M11Wiring.routedW2M11` | `A04M11Wiring.w2M11Supply` |
| `w2M1k` aligned (in `A04M1kWiring`) | `A04M1kWiring.routedW2M1kAligned` | `A04M1kWiring.m1kAlignedSupply` |
| `w2M1k` separated (in `A04M1kWiring`) | `A04M1kWiring.routedW2M1kSeparated` | `A04M1kWiring.m1kSeparatedSupply` |
| `w3Shift` (in `A04ShiftWiring`) | `A04ShiftWiring.routedW3Shift` | `A04ShiftWiring.w3ShiftSupply` |
| `w2R1` (in `A04R1Wiring`) | `A04R1Wiring.routedW2R1` | `A04R1Wiring.w2R1Supply` |
| `w3Nd2CoarseFine` | `routedNd2` | `A04FourTags.nd2Supply` |
| `w3Nd3CoarseFine` | `routedNd3` | `A04FourTags.nd3Supply` |
| `w4` | `routedW4` | `A04FourTags.w4Supply` |

so a state whose classification at every wall is one of these tags has a
`PresentedProgress`.  All ten tags have constructors; the four tags with no
constructor in this file, `w2M11`, `w2M1k`, `w3Shift` and `w2R1`, are routed in
their own modules. -/

section Classification

open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.SemanticAtlasMarch

variable {baseStart baseFinish : coordinate → ℚ}

/-- **Presented progress from a routed classification.**  The `Nonempty` form of
`presentedProgressOfRoutedWalls`: at every coordinate the state's classification
is one of the seven tags above, each of which inhabits `RoutedWall`. -/
noncomputable def presentedProgressOfRoutedClassification
    (current : State degree (atlasChartMatrix coordinate degree) baseStart baseFinish)
    (routed : ∀ (wall : coordinate), current.FirstWall wall →
      Nonempty (RoutedWall degree coordinate
        (atlasChartMatrix coordinate degree current.toMatrixState.label) wall))
    (hA02Generic : SimpleNegativeCrossings current.toMatrixState.currentStart
      current.toMatrixState.currentFinish) :
    current.PresentedProgress :=
  presentedProgressOfRoutedWalls current (fun wall hw ↦ (routed wall hw).some)
    hA02Generic

end Classification

end DraismaVargas.LocalCases.A04MoreTags
