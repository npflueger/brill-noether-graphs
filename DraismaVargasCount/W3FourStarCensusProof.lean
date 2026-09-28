import DraismaVargasCount.StarCensusEngine
import DraismaVargasCount.M11StarCensusProof
import DraismaVargasCount.RegrowthBalances
import DraismaVargasCount.W3Nd2StarCensusProof

/-!
# The W3Four star census, Stages 1 and 3, and Stage 2 reduced to transports

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w3-r1-nd3-t2-(a=k4)}`,
Figure 28 and Equation (2); Vargas, Part II (arXiv:2609.09109): the star of a
codimension-one wall and `prop-signed-mult`.  Part I works with gluing data up to
isomorphism, which allows a branch swap above each branch; here the members `M⁽¹⁾` and
`M⁽²⁾` of Figure 28 are built on branch-swapped copies of the wall datum.  Engine
`StarCensusEngine`; the same pattern as `W3Nd3StarCensusProof` and
`M11StarCensusProof`.  This is the W3Four case of the star parity in step 2 of
`Assembly`: exhaustion of the star, and uniqueness with multiplicity.  The census
splits into (a) every nonsingular position is a star class (Stage 1), (b) every star
class is a position (Stage 2), and (c) distinct positions are distinct classes
(Stage 3).

## The result, in one paragraph

`RegrowthWallInput.FamilyStarParity (2+2) (4*2+2) (6*2+3) .w3Four` is reduced to the single
residue `W3FourStarExhaustion` (`familyStarParity_w3Four_of_exhaustion`), which is
*equivalent* to the census `W3FourStarCensus` (`w3FourStarExhaustion_iff`) and to the count
`W3FourStarCard` ("the star has exactly as many classes as Equation (2) has nonsingular
positions", `w3FourStarExhaustion_iff_card`).  Stages (a) and (c) hold at every core,
degree, positive request and setup **with no hypothesis**: every nonsingular position of
Equation (2) is a star class with its term's multiplicity (`Setup.rep`,
`Setup.multNat_rep`), and **no two of the four positions are ever frame isomorphic**
(`Setup.rep_eq_of_cls_eq`).  Every `w3Four` regrowth carries a setup (`exists_setup`), and
Equation (2) holds at it with no incoming-member receipt (`Setup.sum_signedMult`).

## The route, and why the existing balance could not be consumed as stated

`RegrowthBalances.exists_w3Four_balance` returns Equation (2) over a
`W3FourRegrownColumnSeam.MemberCertificates` opened from an existential.  Its dictionaries
`certified.dictionary i` are bare `StableGraphIncidence.Equivalence`s with no retained-column
property exported, so the engine's `hRetained` cannot be proved for them, and the members'
bases and gauges are forgotten.  This file therefore keeps Part I's data as **data**:
`Setup` records the W3 input, the nd3 profile, the branch region and the two gauge moves of
`W3FourClosure.exists_member_one`/`_two`; the four members are rebuilt from it exactly as
`W3FourRegrownColumn.exists_figure28Receipts_honest` builds them (`Setup.cd`,
`Setup.receipts`), and Equation (2) is re-proved on them by
`W3FourCountBalance.exists_sum_signedMult_eq_zero`'s own argument (`Setup.balance`).  The
one full-dimensional member that argument needs is not the regrowth's cover: every
nonsingular position is presented from the regrowth's own frame through its own dictionary
(`RegrowthBalances.regrowthPresentation`, `Setup.fdAt`).  So the mismatch between the
balance's family and the regrowth's cover is sidestepped rather than repaired: nothing
here identifies the regrowth's cover with a member of this family, and nothing needs to.

## What is proved

* **Setup** (§1).  `Setup` and its derived objects: `geometry`, `lab`, `rows`, the gauges
  `gaugeOne`/`gaugeTwo`, `cdOne`…`cdFour`, `cd`, `receipts`, `presentation_eq`;
  `balance` (Equation (2) given full-dimensional nonsingular members).
* **Gauged members** (§2).  `graphData_branchSquare` (the anchor branch square of any
  `LimitChainCore.GraphData`, generic); `GaugeAnchor` (a hypothesis shaper: dictionary to
  the gauge copy with the gauge's rows, and an inverse isomorphism), `GaugeAnchor.E`,
  `E_row`, `retained`, `gaugedMerge`, `branchSquare`, `rowSquare`, `member`,
  `multNat_member`; the two anchors `GaugeAnchor.refl` (`M⁽³⁾`, `M⁽⁴⁾`) and
  `GaugeAnchor.swap` (`M⁽¹⁾`, `M⁽²⁾`, through the inverse branch swap).
* **Stage 1 (a)** (§3).  `signedMult_congr`, `absMult_ne_zero_iff` (any coordinates);
  `Setup.anchor`, `Nonsingular`, `honest`, `honest_matrix`, `engLab`, `absMult_engLab`,
  `engLab_det_ne_zero`, `fdAt`, `sum_signedMult`, `signedMult_eq_zero`,
  `integral_signedMult`, `rep`, `multNat_rep`.
* **Stage 3 (c)** (§4).  `frameIso_side` (generic: a frame isomorphism between two
  positions of one wall preserves or complements the side assignment on the wall
  occurrences), `false_of_side_rightOf`, `false_of_selected_eq`; `Setup.isolated`,
  `right_eq`, `side_of_frameIso`, `not_rel_of_isolated_ne` (members isolating different
  directions), `matrix_none_presented`, `not_rel_01` (`M⁽¹⁾` against `M⁽²⁾`, by the regrown
  column), `rep_eq_of_cls_eq`.
* **Census at one wall** (§5).  `repCls`, `repCls_injective`, `Exhausts`,
  `census_of_exhaustion`, `exhaustion_of_census`, `card_nonsingular_le`,
  `exhausts_iff_card`, `card_nonsingular_ne_one`, `starParityAt_of_exhaustion`.
* **Family clause** (§6).  `exists_setup`, `W3FourStarCensus`,
  `familyStarParity_w3Four_of_census`, `W3FourStarExhaustion`,
  `w3FourStarCensus_of_exhaustion`, `exhaustion_of_w3FourStarCensus`,
  `w3FourStarExhaustion_iff`, `W3FourStarCard`, `w3FourStarExhaustion_iff_card`,
  `familyStarParity_w3Four_of_exhaustion`.
* **Stage 2 reduced to transports** (§7).  `GaugeAnchor.cls_eq_of_transport`,
  `Setup.PositionTransport`, `Setup.exhausts_of_transports`.
* **Which positions are singular** (§8).  `nonsingular_zero_iff` … `nonsingular_three_iff`:
  `M⁽²⁾`, `M⁽³⁾`, `M⁽⁴⁾` are singular exactly when `c(e₄)`, `c(e₂)`, `c(e₃)` vanish, `M⁽¹⁾`
  exactly when `c(e₂)/k₂ + c(e₃)/k₃ = c(e₄)/k₄`.

## What is NOT proved here (every hypothesis, explicitly)

* **`FamilyStarParity (2+2) (4*2+2) (6*2+3) .w3Four` is not proved here.**  Its exact
  residue is `W3FourStarExhaustion` (Stage 2 (b)): every star member is a frame isomorph
  of a nonsingular position.  *Interface*: equivalent to `W3FourStarCensus` and to
  `W3FourStarCard`.  It is proved in `W3FourStarExhaustionProof`.  No regrowth tagged
  `w3Four` is exhibited here.  Computer experiments with genus-six W3Four walls are
  consistent with the census: every such wall seen has two or three classes (never one
  and never four), consistent with `card_nonsingular_ne_one` and with the side invariant
  (when two classes have the same split, they are `M⁽¹⁾` and `M⁽²⁾`).
* **What Stage 2 needs** (the hypothesis of `Setup.exhausts_of_transports`, not proved
  here): for each star member `m` with limit isomorphism `ψ`, a placement and a
  `ResolutionExpansionFree.TransportFree` along `ψ ≫ φᵢ⁻¹` onto position `i`'s pasted
  resolution.  As in `M11StarExhaustionProof` this needs (i) the wall's `W3SourceInput`
  and `Nd3Profile` pulled back to `m.limit` along `ψ` (§5 of `M11StarExhaustionProof` is
  the W2 analogue); (ii) Part I's incoming partition census for case `(a = k₄)` at `m`,
  in relational form; (iii) the four pasted resolutions' shapes as relations; and
  (iv) a dichotomy deciding which of the two branch-swapped positions receives a member
  isolating `t₄`, and the corresponding endpoint compatibility, fed to
  `M11StarExhaustionProof.nonempty_transportFree_of_rel`.
* No new separation, balance or multiplicity input is assumed anywhere.

## Tempting inferences, checked

* (i) *"Four positions, some may be singular; (c) is needed only among the nonsingular
  ones."*  **Holds**, and is exact in Lean: §8 says which positions are singular (a
  vanishing cofactor), and `card_nonsingular_ne_one` rules out one nonsingular position.
  But (c) is in fact proved among **all** positions: `rep_eq_of_cls_eq` has no
  singularity content.
* (ii) *"The split members over branch-swapped bases are the analogue of M-11's remote
  position; anchor them through the branch isomorphism."*  **Holds**, for **both** `M⁽¹⁾`
  and `M⁽²⁾`, each at its own copy (`GaugeAnchor.swap`, two different permutations): the
  anchor is the gauge copy, `φ` the inverse relabelling, exactly `M11StarCensusProof.member1`.
* (iii) *"The crossed-column separation or the matrix separation of the other W3 cases
  may cover (c); if two positions can be isomorphic, does parity still follow?"*
  **Neither covers it; no two positions are ever isomorphic.**  The determinant trick of
  `W3Nd2StarCensusProof` fails for `M⁽¹⁾`/`M⁽²⁾` (their determinants are not forced
  apart), and the crossed identity of `W3Nd3StarCensusProof` has no analogue.  What works
  is a new, family-free **side invariant** (`frameIso_side`) for the five pairs isolating
  different directions, and for `M⁽¹⁾`/`M⁽²⁾` (both isolating `t₄`, both with background
  `t₄`) the regrown column: equality would force `[e₂]/k₂ + [e₃]/k₃ = [e₄]/(k₂+k₃-1)` row by
  row, which never holds (`false_of_selected_eq`).  Parity follows from the census.
* `RegrowthBalances.exists_w3Four_balance` is accurate but not consumable by the engine
  (its dictionaries are opaque), so it is not used; the family is rebuilt as `Setup`,
  and the balance re-proved on it by the same argument.

## Consumers

`W3FourStarExhaustionProof`, and through it the `w3Four` clause of the star parity
(step 2 of `Assembly`).
-/

namespace DraismaVargas.Count.W3FourStarCensusProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open ThirdEquation W3R1SourceProfile
open W3FourClosure (FourStarGeometry ofGrowProfile)
open W3FourSourceCandidates (growProfileFirst growProfileSecond)
open W3FourStableGraph W3FourSurvival W3FourRegrownColumn
open LimitChainCore (Gauge GraphData)

/-- Figure 28's family is stated with a classical decision procedure on the target's
edges (`W3FourStableGraph`); this local instance makes the statements below elaborate
against it. -/
noncomputable local instance instDecidableEqEdgesF5 {target : CFGraph} :
    DecidableEq target.edges := Classical.decEq _

/-! ## 1.  Part I's data at a `w3Four` regrowth, and Figure 28's family built from it -/

section Setup

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Part I's data at a `w3Four` regrowth**: the W3 input and nd3 profile of the case
`(a = k₄)`, the branch region through `t₃`, and the two branch-swapped gauge copies
carrying Figure 28's `M⁽¹⁾` and `M⁽²⁾` (`W3FourClosure.exists_member_one`/`_two`). -/
structure Setup (w : Regrowth core y degree) where
  star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)
  input : W3SourceInput w.limit star
  profile : Nd3Profile w.limit input.distinguishedBlock
  directions : profile.first.1.1.1 ≠ profile.second.1.1.1
  largest_index : w.limit.sourceEdgeIndex profile.largest.1 =
    (w.limit.vertexPartition (mergeVertex w)).blockCard input.distinguishedBlock.1
  root : (w.frame.limitTarget w.column).V
  hRoot : root ≠ mergeVertex w
  hGrowFixed : TargetBranchRegion.edgeMoved (mergeVertex w) root hRoot
    profile.first.1.1.1 = false
  hLargestFixed : TargetBranchRegion.edgeMoved (mergeVertex w) root hRoot
    profile.largest.1.1.1 = false
  hOtherMoved : TargetBranchRegion.edgeMoved (mergeVertex w) root hRoot
    profile.second.1.1.1 = true
  permOne : Equiv.Perm (Fin degree)
  fixOne : ∀ sheet, (w.limit.vertexPartition (mergeVertex w)).Rel (permOne sheet) sheet
  positionOne : W3FourClosure.PositionOne
    (W3FourDisjointness.branchSwapOfPerm w.limit (mergeVertex w) root hRoot permOne
      fixOne).apply (mergeVertex w)
  geomOne : positionOne.toFourStarGeometry =
    (ofGrowProfile (growProfileFirst profile directions largest_index)).swap root hRoot
      permOne fixOne hGrowFixed hLargestFixed hOtherMoved
  indexOneGrow : (positionOne.candidate.resolution
      (ofGrowProfile (growProfileFirst profile directions largest_index)).growAnchor).newEdge.blockCard
      (ofGrowProfile (growProfileFirst profile directions largest_index)).growAnchor =
    (w.limit.edgePartition
      (ofGrowProfile (growProfileFirst profile directions largest_index)).growTarget).blockCard
      (ofGrowProfile (growProfileFirst profile directions largest_index)).growAnchor
  indexOneOther : (positionOne.candidate.resolution
      (ofGrowProfile (growProfileFirst profile directions largest_index)).growAnchor).newEdge.blockCard
      (permOne (ofGrowProfile (growProfileFirst profile directions largest_index)).otherAnchor) =
    (w.limit.edgePartition
      (ofGrowProfile (growProfileFirst profile directions largest_index)).otherTarget).blockCard
      (ofGrowProfile (growProfileFirst profile directions largest_index)).otherAnchor
  permTwo : Equiv.Perm (Fin degree)
  fixTwo : ∀ sheet, (w.limit.vertexPartition (mergeVertex w)).Rel (permTwo sheet) sheet
  positionTwo : W3FourClosure.PositionTwo
    (W3FourDisjointness.branchSwapOfPerm w.limit (mergeVertex w) root hRoot permTwo
      fixTwo).apply (mergeVertex w)
  geomTwo : positionTwo.toFourStarGeometry =
    (ofGrowProfile (growProfileFirst profile directions largest_index)).swap root hRoot
      permTwo fixTwo hGrowFixed hLargestFixed hOtherMoved
  indexTwo : (positionTwo.candidate.resolution
      (ofGrowProfile (growProfileFirst profile directions largest_index)).growAnchor).newEdge.blockCard
      (ofGrowProfile (growProfileFirst profile directions largest_index)).growAnchor + 1 =
    (w.limit.edgePartition
      (ofGrowProfile (growProfileFirst profile directions largest_index)).growTarget).blockCard
      (ofGrowProfile (growProfileFirst profile directions largest_index)).growAnchor +
    (w.limit.edgePartition
      (ofGrowProfile (growProfileFirst profile directions largest_index)).otherTarget).blockCard
      (ofGrowProfile (growProfileFirst profile directions largest_index)).otherAnchor

namespace Setup

variable {w : Regrowth core y degree} (S : Setup w)

/-- `M⁽³⁾`'s grow profile. -/
noncomputable abbrev grownFirst := growProfileFirst S.profile S.directions S.largest_index

/-- `M⁽⁴⁾`'s grow profile. -/
noncomputable abbrev grownSecond := growProfileSecond S.profile S.directions S.largest_index

/-- The four-star geometry of the case. -/
noncomputable abbrev geometry : FourStarGeometry w.limit (mergeVertex w) :=
  ofGrowProfile S.grownFirst

/-- The limit's canonical stable-row labelling. -/
noncomputable abbrev lab : StablePathLabelling w.limit :=
  StablePathLabelling.ofCardEq w.limit S.input.stablePath_card

/-- The limit's displayed rows. -/
noncomputable abbrev rows : LimitRows w.limit (mergeVertex w) S.geometry :=
  W3FourLimitRows.limitRowsOfInput S.grownFirst

/-- `M⁽¹⁾`'s branch swap. -/
noncomputable abbrev relOne : w.limit.SheetRelabeling :=
  W3FourDisjointness.branchSwapOfPerm w.limit (mergeVertex w) S.root S.hRoot S.permOne S.fixOne

/-- `M⁽²⁾`'s branch swap. -/
noncomputable abbrev relTwo : w.limit.SheetRelabeling :=
  W3FourDisjointness.branchSwapOfPerm w.limit (mergeVertex w) S.root S.hRoot S.permTwo S.fixTwo

theorem wallOne : S.relOne.apply.vertexPartition (mergeVertex w) =
    w.limit.vertexPartition (mergeVertex w) :=
  W3FourDisjointness.branchSwapOfPerm_vertexPartition_wall _ _ _ _ _ _

theorem wallTwo : S.relTwo.apply.vertexPartition (mergeVertex w) =
    w.limit.vertexPartition (mergeVertex w) :=
  W3FourDisjointness.branchSwapOfPerm_vertexPartition_wall _ _ _ _ _ _

/-- `M⁽¹⁾`'s gauge. -/
noncomputable abbrev gaugeOne : Gauge w.limit S.relOne.apply (mergeVertex w) :=
  Gauge.ofSheetRelabeling S.relOne S.input.valid.1 S.wallOne

/-- `M⁽²⁾`'s gauge. -/
noncomputable abbrev gaugeTwo : Gauge w.limit S.relTwo.apply (mergeVertex w) :=
  Gauge.ofSheetRelabeling S.relTwo S.input.valid.1 S.wallTwo

theorem validOne : S.relOne.apply.Valid :=
  (W3FourDisjointness.branchSwapOfPerm_branchGauge _ _ _ _ _ _).valid S.input.valid

theorem validTwo : S.relTwo.apply.Valid :=
  (W3FourDisjointness.branchSwapOfPerm_branchGauge _ _ _ _ _ _).valid S.input.valid

theorem survivalOne : SelectedSurvival S.relOne.apply (mergeVertex w)
    S.positionOne.toFourStarGeometry := by
  rw [S.geomOne]
  exact SelectedSurvival.swap S.geometry S.root S.hRoot S.permOne S.fixOne
    (SelectedSurvival.ofGrowProfile S.grownFirst) S.input.valid.1 S.hGrowFixed
    S.hLargestFixed S.hOtherMoved

theorem survivalTwo : SelectedSurvival S.relTwo.apply (mergeVertex w)
    S.positionTwo.toFourStarGeometry := by
  rw [S.geomTwo]
  exact SelectedSurvival.swap S.geometry S.root S.hRoot S.permTwo S.fixTwo
    (SelectedSurvival.ofGrowProfile S.grownFirst) S.input.valid.1 S.hGrowFixed
    S.hLargestFixed S.hOtherMoved

theorem anchorOne : S.positionOne.toFourStarGeometry.growAnchor = S.geometry.growAnchor :=
  congrArg FourStarGeometry.growAnchor S.geomOne

theorem anchorTwo : S.positionTwo.toFourStarGeometry.growAnchor = S.geometry.growAnchor :=
  congrArg FourStarGeometry.growAnchor S.geomTwo

theorem growTargetOne : S.positionOne.toFourStarGeometry.growTarget = S.geometry.growTarget :=
  congrArg FourStarGeometry.growTarget S.geomOne

theorem otherTargetOne :
    S.positionOne.toFourStarGeometry.otherTarget = S.geometry.otherTarget :=
  congrArg FourStarGeometry.otherTarget S.geomOne

theorem otherAnchorOne :
    S.positionOne.toFourStarGeometry.otherAnchor = S.permOne S.geometry.otherAnchor :=
  congrArg FourStarGeometry.otherAnchor S.geomOne

theorem largestOne :
    S.positionOne.toFourStarGeometry.largestTarget = S.geometry.largestTarget :=
  congrArg FourStarGeometry.largestTarget S.geomOne

theorem largestTwo :
    S.positionTwo.toFourStarGeometry.largestTarget = S.geometry.largestTarget :=
  congrArg FourStarGeometry.largestTarget S.geomTwo

theorem largestAnchorTwo :
    S.positionTwo.toFourStarGeometry.largestAnchor = S.geometry.largestAnchor :=
  congrArg FourStarGeometry.largestAnchor S.geomTwo

theorem backgroundOne (sheet : Fin degree) :
    S.relOne.apply.sourceEdge S.positionOne.largestTarget sheet =
      S.gaugeOne.edge (w.limit.sourceEdge S.positionOne.largestTarget sheet) := by
  rw [S.largestOne]
  exact branchSwap_sourceEdge_of_fixed S.root S.hRoot S.permOne S.fixOne
    S.geometry.largestTarget S.hLargestFixed sheet

theorem backgroundTwo (sheet : Fin degree) :
    S.relTwo.apply.sourceEdge S.positionTwo.largestTarget sheet =
      S.gaugeTwo.edge (w.limit.sourceEdge S.positionTwo.largestTarget sheet) := by
  rw [S.largestTwo]
  exact branchSwap_sourceEdge_of_fixed S.root S.hRoot S.permTwo S.fixTwo
    S.geometry.largestTarget S.hLargestFixed sheet

theorem rowGrowOne : S.rows.rowGrow =
    gaugeRow S.lab S.gaugeOne S.survivalOne.grow_survives := by
  refine (gaugeRow_eq_of_edge S.lab S.gaugeOne S.survivalOne.grow_survives
    (W3FourLimitRows.grow_survives S.grownFirst) ?_).symm
  rw [S.growTargetOne, S.anchorOne, branchSwap_sourceEdge_of_fixed S.root S.hRoot
    S.permOne S.fixOne S.geometry.growTarget S.hGrowFixed S.geometry.growAnchor]
  exact congrArg S.gaugeOne.edge (GluingDatum.sourceEdge_self w.limit S.grownFirst.grow.1)

theorem rowOtherOne : S.rows.rowOther =
    gaugeRow S.lab S.gaugeOne S.survivalOne.other_survives := by
  refine (gaugeRow_eq_of_edge S.lab S.gaugeOne S.survivalOne.other_survives
    (W3FourLimitRows.other_survives S.grownFirst) ?_).symm
  rw [S.otherTargetOne, S.otherAnchorOne, branchSwap_sourceEdge_of_moved S.root S.hRoot
    S.permOne S.fixOne S.geometry.otherTarget S.hOtherMoved S.geometry.otherAnchor]
  exact congrArg S.gaugeOne.edge (GluingDatum.sourceEdge_self w.limit S.grownFirst.other.1)

theorem rowLargestTwo : S.rows.rowLargest =
    gaugeRow S.lab S.gaugeTwo S.survivalTwo.largest_survives := by
  refine (gaugeRow_eq_of_edge S.lab S.gaugeTwo S.survivalTwo.largest_survives
    (W3FourLimitRows.largest_survives S.grownFirst) ?_).symm
  rw [S.largestTwo, S.largestAnchorTwo, branchSwap_sourceEdge_of_fixed S.root S.hRoot
    S.permTwo S.fixTwo S.geometry.largestTarget S.hLargestFixed S.geometry.largestAnchor]
  exact congrArg S.gaugeTwo.edge (GluingDatum.sourceEdge_self w.limit S.grownFirst.largest.1)

/-- `M⁽¹⁾`, packaged for the regrown column (as in
`W3FourRegrownColumn.exists_figure28Receipts_honest`). -/
noncomputable def cdOne : ColumnData w.limit (mergeVertex w) S.geometry S.lab :=
  positionOneColumnData S.positionOne S.survivalOne S.validOne S.geometry S.lab S.gaugeOne
    (by rw [S.anchorOne]; exact rfl) S.backgroundOne S.rows.rowGrow S.rows.rowOther
    S.rowGrowOne S.rowOtherOne S.geometry.growAnchor (S.permOne S.geometry.otherAnchor)
    S.anchorOne.symm S.otherAnchorOne.symm

/-- `M⁽²⁾`, packaged for the regrown column. -/
noncomputable def cdTwo : ColumnData w.limit (mergeVertex w) S.geometry S.lab :=
  positionTwoColumnData S.positionTwo S.survivalTwo S.validTwo S.geometry S.lab S.gaugeTwo
    (by rw [S.anchorTwo]; exact rfl) S.backgroundTwo S.rows.rowLargest S.rowLargestTwo
    S.geometry.growAnchor S.anchorTwo.symm

/-- `M⁽³⁾`, packaged for the regrown column. -/
noncomputable def cdThree : ColumnData w.limit (mergeVertex w) S.geometry S.lab :=
  growColumnData S.grownFirst (SelectedSurvival.ofGrowProfile S.grownFirst) S.input.valid
    S.geometry S.lab rfl S.rows.rowGrow
    (growRow_eq_rowOf S.lab S.grownFirst (SelectedSurvival.ofGrowProfile S.grownFirst)
      (W3FourLimitRows.grow_survives S.grownFirst)).symm S.geometry.growAnchor rfl

/-- `M⁽⁴⁾`, packaged for the regrown column. -/
noncomputable def cdFour : ColumnData w.limit (mergeVertex w) S.geometry S.lab :=
  growColumnData S.grownSecond (SelectedSurvival.ofGrowProfile S.grownSecond) S.input.valid
    S.geometry S.lab S.geometry.other_wall_rel S.rows.rowOther
    (growRow_eq_rowOf S.lab S.grownSecond (SelectedSurvival.ofGrowProfile S.grownSecond)
      (W3FourLimitRows.other_survives S.grownFirst)).symm S.geometry.otherAnchor rfl

/-- The four members, in Equation (2)'s order. -/
noncomputable def cd : Fin 4 → ColumnData w.limit (mergeVertex w) S.geometry S.lab :=
  ![S.cdOne, S.cdTwo, S.cdThree, S.cdFour]

theorem relAnchorOne : (S.relOne.apply.vertexPartition (mergeVertex w)).Rel
    S.positionOne.toFourStarGeometry.growAnchor S.geometry.growAnchor :=
  congrArg (S.relOne.apply.vertexPartition (mergeVertex w)).repr S.anchorOne

theorem relAnchorTwo : (S.relTwo.apply.vertexPartition (mergeVertex w)).Rel
    S.positionTwo.toFourStarGeometry.growAnchor S.geometry.growAnchor :=
  congrArg (S.relTwo.apply.vertexPartition (mergeVertex w)).repr S.anchorTwo

theorem relOtherOne : (S.relOne.apply.vertexPartition (mergeVertex w)).Rel
    S.positionOne.toFourStarGeometry.growAnchor (S.permOne S.geometry.otherAnchor) := by
  rw [S.wallOne, S.anchorOne]
  exact S.geometry.other_wall_rel.trans (S.fixOne S.geometry.otherAnchor).symm

/-- **Figure 28's receipts, over the limit's own rows**, built from the setup exactly as
`W3FourRegrownColumn.exists_figure28Receipts_honest` builds them. -/
noncomputable def receipts : Figure28Receipts w.limit (mergeVertex w) S.geometry where
  rows := S.rows
  member := fun i ↦ (S.cd i).memberColumn
  otherSheet := S.permOne S.geometry.otherAnchor
  background_one := S.largestOne
  selected_one := rfl
  index_one_grow := by
    change newIndex (S.positionOne.toFourStarGeometry.reversedCandidate
      S.positionOne.fine S.positionOne.fine_refines S.positionOne.grow_refines_fine
      S.positionOne.other_refines_fine S.positionOne.rightCounts) S.geometry.growAnchor = _
    rw [reversedCandidate_newIndex_eq_blockCard S.positionOne.toFourStarGeometry
      S.positionOne.fine S.positionOne.fine_refines S.positionOne.grow_refines_fine
      S.positionOne.other_refines_fine S.positionOne.rightCounts S.relAnchorOne, S.anchorOne]
    exact S.indexOneGrow
  index_one_other := by
    change newIndex (S.positionOne.toFourStarGeometry.reversedCandidate
      S.positionOne.fine S.positionOne.fine_refines S.positionOne.grow_refines_fine
      S.positionOne.other_refines_fine S.positionOne.rightCounts)
      (S.permOne S.geometry.otherAnchor) = _
    rw [reversedCandidate_newIndex_eq_blockCard S.positionOne.toFourStarGeometry
      S.positionOne.fine S.positionOne.fine_refines S.positionOne.grow_refines_fine
      S.positionOne.other_refines_fine S.positionOne.rightCounts S.relOtherOne, S.anchorOne]
    exact S.indexOneOther
  background_two := S.largestTwo
  selected_two := rfl
  index_two := by
    change newIndex (S.positionTwo.toFourStarGeometry.reversedCandidate
      S.positionTwo.fine S.positionTwo.fine_refines S.positionTwo.grow_refines_fine
      S.positionTwo.other_refines_fine S.positionTwo.rightCounts) S.geometry.growAnchor + 1 = _
    rw [reversedCandidate_newIndex_eq_blockCard S.positionTwo.toFourStarGeometry
      S.positionTwo.fine S.positionTwo.fine_refines S.positionTwo.grow_refines_fine
      S.positionTwo.other_refines_fine S.positionTwo.rightCounts S.relAnchorTwo, S.anchorTwo]
    exact S.indexTwo
  background_three := rfl
  selected_three := rfl
  index_three := growCandidate_newIndex_grow S.grownFirst
  background_four := rfl
  selected_four := rfl
  index_four := growCandidate_newIndex_grow S.grownSecond


/-- The receipts' presentation of a member is its solo presentation over the limit's own
rows. -/
theorem presentation_eq (i : Fin 4) :
    S.receipts.presentation i = soloPresentation (S.cd i).memberColumn (W3FourLimitRows.stableRowPath S.lab) :=
  rfl

/-- **Equation (2) on the setup's own receipts**, given a full-dimensional presentation of
every nonsingular member (in any coordinates).  The proof is
`W3FourCountBalance.exists_sum_signedMult_eq_zero`'s, run on these receipts. -/
theorem balance
    (fdAt : ∀ i : Fin 4, (GluingDatum.LengthMatrixPresentation.matrix
        (S.receipts.presentation i)).det ≠ 0 →
      FullDimensionalSourcePresentation (S.cd i).rowData.candidate.datum (Fin p)) :
    ∑ i : Fin 4, signedMult (S.receipts.presentation i) = 0 := by
  apply W3FourMultiplicityBalance.sum_signedMult_eq_zero_of_receipts S.receipts
  · intro position
    fin_cases position
    · exact W3FourCountBalance.leafCount_of_rightOf S.positionOne.candidate
        S.positionOne.toFourStarGeometry.largestTarget S.positionOne.toFourStarGeometry.growTarget
        S.positionOne.toFourStarGeometry.largestTarget_mem
        S.positionOne.toFourStarGeometry.growTarget_mem
        S.positionOne.toFourStarGeometry.grow_ne_largest rfl
    · exact W3FourCountBalance.leafCount_of_rightOf S.positionTwo.candidate
        S.positionTwo.toFourStarGeometry.largestTarget S.positionTwo.toFourStarGeometry.growTarget
        S.positionTwo.toFourStarGeometry.largestTarget_mem
        S.positionTwo.toFourStarGeometry.growTarget_mem
        S.positionTwo.toFourStarGeometry.grow_ne_largest rfl
    · exact W3FourCountBalance.leafCount_of_rightOf S.grownFirst.growCandidate
        S.grownFirst.growTarget S.grownFirst.otherTarget S.grownFirst.growTarget_mem
        S.grownFirst.otherTarget_mem S.grownFirst.grow_target_ne_other.symm rfl
    · exact W3FourCountBalance.leafCount_of_rightOf S.grownSecond.growCandidate
        S.grownSecond.growTarget S.grownSecond.otherTarget S.grownSecond.growTarget_mem
        S.grownSecond.otherTarget_mem S.grownSecond.grow_target_ne_other.symm rfl
  · intro hDet
    have fd := fdAt 0 hDet
    change FullDimensionalSourcePresentation S.positionOne.candidate.datum (Fin p) at fd
    constructor
    · rw [W3FourCountBalance.rowDen_grow S.grownFirst S.receipts rfl]
      change w.limit.sourceEdgeIndex S.grownFirst.grow.1 ∣ _
      apply W3FourReversedDenominator.index_dvd_positionOne_swapped
        S.grownFirst S.root S.hRoot S.permOne S.fixOne S.hGrowFixed S.hLargestFixed
        S.hOtherMoved S.positionOne S.geomOne fd
      exact ⟨W3FourLimitRows.grow_survives S.grownFirst,
        W3FourCountBalance.stablePath_eq_sourceEdge _ _⟩
    constructor
    · rw [W3FourCountBalance.rowDen_other S.grownFirst S.receipts rfl]
      change w.limit.sourceEdgeIndex S.grownFirst.other.1 ∣ _
      apply W3FourReversedDenominator.index_dvd_positionOne_swapped
        S.grownFirst S.root S.hRoot S.permOne S.fixOne S.hGrowFixed S.hLargestFixed
        S.hOtherMoved S.positionOne S.geomOne fd
      exact ⟨W3FourLimitRows.other_survives S.grownFirst,
        W3FourCountBalance.stablePath_eq_sourceEdge _ _⟩
    · rw [W3FourCountBalance.rowDen_largest S.grownFirst S.receipts rfl]
      change w.limit.sourceEdgeIndex S.grownFirst.largest.1 ∣ _
      apply W3FourReversedDenominator.index_dvd_positionOne_swapped
        S.grownFirst S.root S.hRoot S.permOne S.fixOne S.hGrowFixed S.hLargestFixed
        S.hOtherMoved S.positionOne S.geomOne fd
      exact ⟨W3FourLimitRows.largest_survives S.grownFirst,
        W3FourCountBalance.stablePath_eq_sourceEdge _ _⟩
  · intro position hDet
    fin_cases position
    · have fd := fdAt 1 hDet
      change FullDimensionalSourcePresentation S.positionTwo.candidate.datum (Fin p) at fd
      change W3FourMultiplicityBalance.rowDen S.receipts S.receipts.rows.rowLargest =
        indexLargest S.geometry
      rw [W3FourCountBalance.rowDen_largest S.grownFirst S.receipts rfl]
      change TrivalentWeight.incomingRowDenominator w.limit _ =
        w.limit.sourceEdgeIndex S.grownFirst.largest.1
      exact W3FourReversedDenominator.incomingRowDenominator_positionTwo_swapped
        S.grownFirst S.root S.hRoot S.permTwo S.fixTwo S.hGrowFixed S.hLargestFixed
        S.hOtherMoved S.positionTwo S.geomTwo fd
    · have fd := fdAt 2 hDet
      change FullDimensionalSourcePresentation S.grownFirst.growCandidate.datum (Fin p) at fd
      change W3FourMultiplicityBalance.rowDen S.receipts S.receipts.rows.rowGrow =
        indexGrow S.geometry
      rw [W3FourCountBalance.rowDen_grow S.grownFirst S.receipts rfl]
      change TrivalentWeight.incomingRowDenominator w.limit _ =
        w.limit.sourceEdgeIndex S.grownFirst.grow.1
      simpa only [W3FourIncomingDenominator.growEdge] using
        W3FourIncomingDenominator.incomingRowDenominator_grow_eq S.grownFirst fd
    · have fd := fdAt 3 hDet
      change FullDimensionalSourcePresentation S.grownSecond.growCandidate.datum (Fin p) at fd
      change W3FourMultiplicityBalance.rowDen S.receipts S.receipts.rows.rowOther =
        indexOther S.geometry
      rw [W3FourCountBalance.rowDen_other S.grownFirst S.receipts rfl]
      have hGrow : S.grownSecond.grow.1 = S.grownFirst.other.1 := rfl
      have hTarget : S.grownSecond.growTarget = S.grownFirst.otherTarget :=
        congrArg (fun edge : w.limit.SourceEdge ↦ edge.1.1) hGrow
      have hAnchor : S.grownSecond.growAnchor = S.grownFirst.otherAnchor :=
        congrArg (fun edge : w.limit.SourceEdge ↦ edge.1.2) hGrow
      change TrivalentWeight.incomingRowDenominator w.limit _ =
        w.limit.sourceEdgeIndex S.grownFirst.other.1
      have result := W3FourIncomingDenominator.incomingRowDenominator_grow_eq S.grownSecond fd
      have hPath : NonDanglingEdge.stablePath
          ⟨w.limit.sourceEdge S.grownFirst.otherTarget S.grownFirst.otherAnchor,
            (SelectedSurvival.ofGrowProfile S.grownFirst).other_survives⟩ =
          (W3FourIncomingDenominator.growEdge S.grownSecond).stablePath := by
        apply congrArg NonDanglingEdge.stablePath
        apply Subtype.ext
        exact congrArg₂ w.limit.sourceEdge hTarget.symm hAnchor.symm
      rw [hPath]
      exact result.trans (congrArg w.limit.sourceEdgeIndex hGrow)

end Setup

end Setup

/-! ## 2.  A Figure 28 member as a member of the wall's star, through its gauge

Every Figure 28 member is a `W3FourRegrownColumn.ColumnData`: a gauge copy `cd.base` of the
limit, the gauge `cd.gauge`, and the member's row descent `cd.rowData` over the copy.  Given
a stable-graph dictionary `G` from the limit to the copy whose rows are the gauge's, and a
geometric isomorphism `φ` from the copy back to the limit undoing `G` on branch vertices and
rows, the member is a member of the wall's star anchored at the copy.  At `M⁽³⁾`, `M⁽⁴⁾`
the gauge is the identity; at `M⁽¹⁾`, `M⁽²⁾` it is the branch swap (inference (ii) of the
module docstring, the analogue of M-11's remote position). -/

section Gauged

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}

/-- **The branch square of any row-descent member, read at its own base**: the member
vertex a source vertex becomes, contracted and read in the base, is that vertex. -/
theorem graphData_branchSquare (rd : GraphData data wall) (vertex : data.SourceVertex) :
    data.sourceEndpoint (contractVertex target wall (rd.branchImage vertex).1.1)
        (rd.branchImage vertex).1.2 = vertex := by
  classical
  have hContract : ∀ (place : Vertex target) (sheet : Fin degree),
      data.sourceEndpoint (contractVertex target wall
          (rd.candidate.datum.sourceEndpoint place sheet).1.1)
        (rd.candidate.datum.sourceEndpoint place sheet).1.2 =
        data.sourceEndpoint (contractVertex target wall place) sheet :=
    fun place sheet ↦ StarCensusEngine.sourceEndpoint_contract _ data place sheet
      (M11StarCensusProof.candidate_refines rd.candidate place)
  by_cases hAt : vertex.1.1 = wall
  · have hSelf : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    by_cases hSel : (data.vertexPartition wall).Rel rd.selected vertex.1.2
    · rw [rd.branchImage_selected hAt hSel]
      change data.sourceEndpoint (contractVertex target wall
          (rd.candidate.datum.sourceEndpoint (LimitChainCore.wallSide target wall
            rd.selectedSide) rd.selected).1.1)
        (rd.candidate.datum.sourceEndpoint (LimitChainCore.wallSide target wall
            rd.selectedSide) rd.selected).1.2 = vertex
      rw [hContract]
      have hSide : contractVertex target wall
          (LimitChainCore.wallSide target wall rd.selectedSide) = wall := by
        unfold LimitChainCore.wallSide
        split_ifs <;> rfl
      rw [hSide, ← hSelf]
      exact (data.sourceEndpoint_eq_iff wall _ _).mpr ⟨rfl, by
        change (data.vertexPartition wall).repr rd.selected =
          (data.vertexPartition wall).repr
            ((data.sourceEndpoint wall vertex.1.2).1.2)
        rw [hSelf]
        exact hSel⟩
    · rw [rd.branchImage_background hAt hSel, hContract]
      exact hSelf
  · rw [rd.branchImage_away hAt]
    change data.sourceEndpoint (contractVertex target wall
        (rd.candidate.datum.sourceEndpoint (oldVertex target vertex.1.1) vertex.1.2).1.1)
      (rd.candidate.datum.sourceEndpoint (oldVertex target vertex.1.1) vertex.1.2).1.2 = vertex
    rw [hContract]
    exact data.sourceEndpoint_self vertex

end Gauged

section GaugedMember

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {geometry : FourStarGeometry w.limit (mergeVertex w)} {labelling : StablePathLabelling w.limit}

/-- **How a Figure 28 member's gauge copy is anchored at the wall**: a stable-graph
dictionary `G` from the limit to the copy whose rows are the gauge's rows, and a geometric
isomorphism `φ` from the copy back to the limit that undoes `G` on branch vertices and on
rows.  Interface: a hypothesis shaper, not a supply; it is inhabited at every
member of every setup (`Setup.anchor`), by the identity at `M⁽³⁾`, `M⁽⁴⁾` and by the branch
swap at `M⁽¹⁾`, `M⁽²⁾`. -/
structure GaugeAnchor (cd : ColumnData w.limit (mergeVertex w) geometry labelling) where
  G : StableGraphIncidence.Equivalence w.limit cd.base
  row_eq : ∀ path, G.row path = cd.gauge.row path
  φ : GeometricDatumIso cd.base w.limit
  vertex_eq : ∀ v : BranchVertex w.limit, φ.sourceVertexEquiv (G.vertex v).1 = v.1
  row_back : ∀ (hConnected : cd.base.Connected) (e : NonDanglingEdge cd.base),
    G.row (φ.stablePathEquiv hConnected e.stablePath) = e.stablePath
  genus_eq : genus cd.base.sourceGraph = genus w.limit.sourceGraph

variable {w}
variable (cd : ColumnData w.limit (mergeVertex w) geometry labelling) (A : GaugeAnchor w cd)

/-- The member's stable-graph dictionary from the wall's limit. -/
noncomputable def GaugeAnchor.E : StableGraphIncidence.Equivalence w.limit
    cd.rowData.candidate.datum :=
  A.G.trans cd.rowData.equivalence

theorem GaugeAnchor.E_row (path : StablePath w.limit) :
    (A.E cd).row path = cd.rowData.stablePathEquiv (cd.gauge.row path) := by
  change cd.rowData.stablePathEquiv (A.G.row path) = _
  rw [A.row_eq]

/-- **The member's retained columns are the wall's.** -/
theorem GaugeAnchor.retained (path : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges) :
    StableSourceMatrix.matrix cd.rowData.candidate.datum ((A.E cd).row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w)
          cd.rowData.candidate.right (some place)) =
      StableSourceMatrix.matrix w.limit path place := by
  rw [A.E_row cd path, cd.rowData.matrix_retained, cd.gauge.matrix_gauge]

theorem gaugedMerge :
    SheetPartition.join
        (cd.rowData.candidate.datum.vertexPartition
          (oldVertex (w.frame.limitTarget w.column) (mergeVertex w)))
        (cd.rowData.candidate.datum.vertexPartition
          (freshVertex (w.frame.limitTarget w.column))) =
      cd.base.vertexPartition (mergeVertex w) :=
  M11StarCensusProof.candidate_merge _ (cd.gauge.wall_eq.trans (M11StarCensusProof.wall_join w))

/-- **The branch square of the member.** -/
theorem GaugeAnchor.branchSquare :
    StarCensusEngine.BranchSquare w cd.base A.φ (E := A.E cd) := by
  intro v
  have h := graphData_branchSquare cd.rowData (A.G.vertex v).1
  change A.φ.sourceVertexEquiv (cd.base.sourceEndpoint
    (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
      (cd.rowData.branchImage (A.G.vertex v).1).1.1)
    (cd.rowData.branchImage (A.G.vertex v).1).1.2) = v.1
  rw [h]
  exact A.vertex_eq v

/-- **The row square of the member.** -/
theorem GaugeAnchor.rowSquare :
    StarCensusEngine.RowSquare w cd.base A.φ (E := A.E cd) := by
  intro e e' he
  change cd.rowData.stablePathEquiv (A.G.row (A.φ.stablePathEquiv _ e.stablePath)) = _
  rw [A.row_back]
  exact M11StarCensusProof.retainedEdge_stablePath cd.rowData.candidate _ e e' he

/-- **The member is a member of the wall's star**, for any full-dimensional presentation
of its datum. -/
noncomputable def GaugeAnchor.member
    (fd : FullDimensionalSourcePresentation cd.rowData.candidate.datum (Fin p)) :
    GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy) (E := A.E cd) (fd := fd)
    (hRetained := A.retained cd) (M := cd.base) (φ := A.φ)
    (hMerge := gaugedMerge cd) (hOld := M11StarCensusProof.candidate_old _)
    (hEdge := M11StarCensusProof.candidate_edge _) (A.branchSquare cd) (A.rowSquare cd)

/-- Its class multiplicity is its own labelling's. -/
theorem GaugeAnchor.multNat_member
    (fd : FullDimensionalSourcePresentation cd.rowData.candidate.datum (Fin p)) :
    (GeometricStar.Star.toFibre (GaugeAnchor.member hy cd A fd).cls).multNat =
      (signedMult (StarCensusEngine.labelling w hy cd.rowData.candidate.datum
        (A.E cd)).presentation).num.natAbs := rfl

end GaugedMember

section Anchors

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  {geometry : FourStarGeometry w.limit (mergeVertex w)} {labelling : StablePathLabelling w.limit}

/-- **The identity anchor**, for a member over the limit itself. -/
noncomputable def GaugeAnchor.refl (cd : ColumnData w.limit (mergeVertex w) geometry labelling)
    (hBase : cd.base = w.limit) (hGauge : HEq cd.gauge (Gauge.refl w.limit (mergeVertex w))) :
    GaugeAnchor w cd := by
  obtain ⟨base, gauge, rowData, anchor_rel, background_sourceEdge, selectedSheets,
    selected_mem, selected_nodup, selected_exhaustive⟩ := cd
  subst hBase
  cases hGauge
  exact { G := StableGraphIncidence.Equivalence.refl w.limit
          row_eq := fun _ ↦ rfl
          φ := GeometricDatumIso.refl w.limit
          vertex_eq := fun _ ↦ rfl
          row_back := fun hConnected e ↦ by
            rw [GeometricDatumIso.stablePathEquiv_refl]
            rfl
          genus_eq := rfl }

/-- **The branch-swap anchor**, for a member over a sheet-relabelled copy of the limit:
`G` is the relabelling's stable-graph dictionary and `φ` the inverse relabelling (the
anchoring of M-11's remote split, `M11StarCensusProof.member1`). -/
noncomputable def GaugeAnchor.swap (cd : ColumnData w.limit (mergeVertex w) geometry labelling)
    (relabeling : w.limit.SheetRelabeling) (hConnected : w.limit.Connected)
    (hWall : relabeling.apply.vertexPartition (mergeVertex w) =
      w.limit.vertexPartition (mergeVertex w))
    (hBase : cd.base = relabeling.apply)
    (hGauge : HEq cd.gauge (Gauge.ofSheetRelabeling relabeling hConnected hWall)) :
    GaugeAnchor w cd := by
  obtain ⟨base, gauge, rowData, anchor_rel, background_sourceEdge, selectedSheets,
    selected_mem, selected_nodup, selected_exhaustive⟩ := cd
  subst hBase
  cases hGauge
  exact { G := StableGraphIncidence.sheetRelabel relabeling hConnected
          row_eq := fun _ ↦ rfl
          φ := (GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling relabeling)).symm
          vertex_eq := fun v ↦ Subtype.ext (Prod.ext rfl (Equiv.symm_apply_apply _ _))
          row_back := fun hC e ↦ by
            rw [GeometricDatumIso.stablePathEquiv_mk]
            change SheetRelabelStable.stablePathEquiv relabeling hConnected
              (NonDanglingEdge.stablePath _) = _
            rw [SheetRelabelStable.stablePathEquiv_mk]
            apply congrArg NonDanglingEdge.stablePath
            apply Subtype.ext
            apply Subtype.ext
            exact Prod.ext rfl (Equiv.apply_symm_apply _ _)
          genus_eq := relabeling.sourceGraphLaplacianEquiv.genus_eq }

end Anchors

/-! ## 3.  Equation (2)'s positions as star classes (Stage 1 (a)) -/

/-- A presentation's multiplicity depends only on its length matrix. -/
theorem signedMult_congr {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    {first second : data.LengthMatrixPresentation coordinate}
    (h : GluingDatum.LengthMatrixPresentation.matrix first =
      GluingDatum.LengthMatrixPresentation.matrix second) :
    signedMult first = signedMult second := by
  unfold signedMult denominatorProduct rowDenominator
  rw [h]

/-- `absMult ≠ 0` is nonsingularity, in any coordinates. -/
theorem absMult_ne_zero_iff {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (presentation : data.LengthMatrixPresentation coordinate) :
    absMult presentation ≠ 0 ↔
      (GluingDatum.LengthMatrixPresentation.matrix presentation).det ≠ 0 := by
  unfold absMult signedMult
  rw [ne_eq, abs_eq_zero, mul_eq_zero, not_or]
  have hD : ((denominatorProduct presentation : ℚ) / 2 ^ leafCount target) ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast (denominatorProduct_pos presentation).ne'
    · exact pow_ne_zero _ two_ne_zero
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hD, h⟩⟩

namespace Setup

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (S : Setup w)

/-- **Every member's anchor**: the branch swap at `M⁽¹⁾`, `M⁽²⁾`, the identity at `M⁽³⁾`,
`M⁽⁴⁾`. -/
noncomputable def anchor : (i : Fin 4) → GaugeAnchor w (S.cd i)
  | ⟨0, _⟩ => GaugeAnchor.swap S.cdOne S.relOne S.input.valid.1 S.wallOne rfl HEq.rfl
  | ⟨1, _⟩ => GaugeAnchor.swap S.cdTwo S.relTwo S.input.valid.1 S.wallTwo rfl HEq.rfl
  | ⟨2, _⟩ => GaugeAnchor.refl S.cdThree rfl HEq.rfl
  | ⟨3, _⟩ => GaugeAnchor.refl S.cdFour rfl HEq.rfl

/-- The nonsingular positions of Equation (2). -/
def Nonsingular (i : Fin 4) : Prop :=
  (GluingDatum.LengthMatrixPresentation.matrix (S.receipts.presentation i)).det ≠ 0

/-- A member's honest labelling in Figure 28's coordinates: the composite row
correspondence `ColumnData.rowEquiv` and the canonical columns. -/
noncomputable def honest (i : Fin 4) :
    StableLengthMatrixLabelling (S.cd i).rowData.candidate.datum
      (Option (w.frame.limitTarget w.column).edges) where
  targetEdge := occurrenceEquiv _ _ (S.cd i).rowData.candidate.right
  row := (S.cd i).rowEquiv.symm

theorem honest_matrix (i : Fin 4) :
    GluingDatum.LengthMatrixPresentation.matrix (S.honest i).presentation =
      GluingDatum.LengthMatrixPresentation.matrix (S.receipts.presentation i) := by
  ext r c
  rw [StableSourceMatrix.labelling_matrix_eq, S.presentation_eq i]
  exact (ColumnData.presented_matrix_eq (S.cd i) r c).symm

variable (hy : Nondegenerate y)

/-- The engine's labelling of member `i`, in the wall's own coordinates. -/
noncomputable abbrev engLab (i : Fin 4) :=
  StarCensusEngine.labelling w hy (S.cd i).rowData.candidate.datum ((S.anchor i).E (S.cd i))

/-- **The engine's multiplicity of a member is its term of Equation (2)**, up to sign. -/
theorem absMult_engLab (i : Fin 4) :
    absMult (S.engLab hy i).presentation = |signedMult (S.receipts.presentation i)| := by
  classical
  let e : Fin p ≃ Option (w.frame.limitTarget w.column).edges :=
    (S.engLab hy i).targetEdge.trans
      (occurrenceEquiv _ _ (S.cd i).rowData.candidate.right).symm
  rw [absMult_labelling_indep (S.engLab hy i) (A04MoreTags.reindexLabelling e (S.honest i)),
    A04MoreTags.reindexLabelling_presentation]
  change absMult (Count.reindex (S.honest i).presentation e) = _
  rw [absMult_reindex]
  unfold absMult
  exact congrArg abs (signedMult_congr (S.honest_matrix i))

theorem engLab_det_ne_zero (i : Fin 4) (h : S.Nonsingular i) :
    (GluingDatum.LengthMatrixPresentation.matrix (S.engLab hy i).presentation).det ≠ 0 := by
  rw [← W4StarParity.absMult_ne_zero_iff, S.absMult_engLab hy i]
  exact (absMult_ne_zero_iff _).mpr h

/-- **The full-dimensional presentation of a nonsingular position**, from the regrowth's
own cover (`RegrowthBalances.regrowthPresentation`) along the member's dictionary. -/
noncomputable def fdAt (i : Fin 4) (h : S.Nonsingular i) :
    FullDimensionalSourcePresentation (S.cd i).rowData.candidate.datum (Fin p) :=
  RegrowthBalances.regrowthPresentation w hy ((S.anchor i).E (S.cd i))
    ((S.cd i).rowData.candidate.datum_valid (S.cd i).rowData.valid)
    ((S.cd i).rowData.genus_eq.trans (S.anchor i).genus_eq)
    (S.engLab hy i) (S.engLab_det_ne_zero hy i h)

include hy in
/-- **Equation (2) at the setup.** -/
theorem sum_signedMult :
    ∑ i : Fin 4, signedMult (S.receipts.presentation i) = 0 :=
  S.balance fun i h ↦ S.fdAt hy i h

/-- A singular position contributes `0`. -/
theorem signedMult_eq_zero (i : Fin 4) (h : ¬ S.Nonsingular i) :
    signedMult (S.receipts.presentation i) = 0 := by
  unfold Nonsingular at h
  rw [not_not] at h
  unfold signedMult
  rw [h, mul_zero]

include hy in
/-- **Every term of Equation (2) is an integer.** -/
theorem integral_signedMult (i : Fin 4) :
    ∃ value : ℤ, signedMult (S.receipts.presentation i) = (value : ℚ) := by
  by_cases h : S.Nonsingular i
  · obtain ⟨value, hv⟩ := isIntegralMultiplicity (S.fdAt hy i h)
    have hAbs := S.absMult_engLab hy i
    unfold absMult at hAbs
    change |signedMult (S.fdAt hy i h).labelling.presentation| = _ at hAbs
    rw [hv] at hAbs
    rcases abs_eq_abs.mp hAbs with h1 | h1
    · exact ⟨value, h1.symm⟩
    · exact ⟨-value, by rw [Int.cast_neg, h1, neg_neg]⟩
  · exact ⟨0, by rw [S.signedMult_eq_zero i h, Int.cast_zero]⟩

/-- **The star member of a nonsingular position of Equation (2).** -/
noncomputable def rep (i : Fin 4) (h : S.Nonsingular i) : GeometricStar.StarMember hy w :=
  GaugeAnchor.member hy (S.cd i) (S.anchor i) (S.fdAt hy i h)

/-- **The multiplicity of a position's class is its term of Equation (2)**, up to sign. -/
theorem multNat_rep (i : Fin 4) (h : S.Nonsingular i) :
    (GeometricStar.Star.toFibre (S.rep hy i h).cls).multNat =
      (signedMult (S.receipts.presentation i)).num.natAbs := by
  change (GeometricStar.Star.toFibre
    (GaugeAnchor.member hy (S.cd i) (S.anchor i) (S.fdAt hy i h)).cls).multNat = _
  rw [GaugeAnchor.multNat_member]
  apply M11StarCensusProof.num_natAbs_eq_of_abs_eq
  exact S.absMult_engLab hy i

end Setup

/-! ## 4.  Separation (Stage 3)

Two invariants of a frame isomorphism between two positions of one wall.

* **The side invariant** (`frameIso_side`): the isomorphism fixes every old column and the
  regrown occurrence, so it either fixes or exchanges the two expanded wall vertices, and
  therefore either preserves or complements the side assignment `right` on the wall
  occurrences.  Figure 28's members isolate `t₄` (`M⁽¹⁾`, `M⁽²⁾`), `t₂` (`M⁽³⁾`) and `t₃`
  (`M⁽⁴⁾`) on one side; three distinct wall directions leave neither possibility between
  two members isolating different directions.
* **The regrown column** (`StarCensusEngine.frameIso_matrix_new`), for `M⁽¹⁾` against
  `M⁽²⁾`, which isolate the same direction: both resolve their background with `t₄`, so a
  frame isomorphism would equate their distinguished regrown contributions
  `[e₂]/k₂ + [e₃]/k₃` and `[e₄]/(k₂+k₃-1)`, which never agree. -/

theorem unorderedEnds_mem {α β : Type*} {f : α ≃ β} {a : α × α} {b : β × β}
    (h : UnorderedEnds f a b) {x : α} (hx : a.1 = x ∨ a.2 = x) : b.1 = f x ∨ b.2 = f x := by
  rcases h with h | h <;> rw [h] <;> rcases hx with hx | hx <;> subst hx <;> simp

section Side

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} {hy : Nondegenerate y}
  {right right' : (w.frame.limitTarget w.column).edges → Bool}
  {D : GluingDatum (graph (w.frame.limitTarget w.column) (mergeVertex w) right) degree}
  {D' : GluingDatum (graph (w.frame.limitTarget w.column) (mergeVertex w) right') degree}
  {E : StableGraphIncidence.Equivalence w.limit D}
  {E' : StableGraphIncidence.Equivalence w.limit D'}
  {fd : FullDimensionalSourcePresentation D (Fin p)}
  {fd' : FullDimensionalSourcePresentation D' (Fin p)}

include hy in
/-- **A frame isomorphism between two positions preserves or complements the side
assignment on the wall occurrences.** -/
theorem frameIso_side
    (hRetained : ∀ (path : StablePath w.limit) (place : (w.frame.limitTarget w.column).edges),
      StableSourceMatrix.matrix D (E.row path)
          (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right (some place)) =
        StableSourceMatrix.matrix w.limit path place)
    (hRetained' : ∀ (path : StablePath w.limit) (place : (w.frame.limitTarget w.column).edges),
      StableSourceMatrix.matrix D' (E'.row path)
          (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right' (some place)) =
        StableSourceMatrix.matrix w.limit path place)
    (fi : GeometricSegmentWalls.FrameIso (StarCensusEngine.frame w hy D E fd)
      (StarCensusEngine.frame w hy D' E' fd')) :
    (∀ e ∈ GluingDatum.incidentEdges (mergeVertex w), right' e = right e) ∨
      (∀ e ∈ GluingDatum.incidentEdges (mergeVertex w), right' e = !right e) := by
  classical
  have hAgree := StarCensusEngine.agreeOffColumnSlot w hy fd fd' hRetained hRetained'
  have hCol : ∀ c : (w.frame.limitTarget w.column).edges, fi.datum.targetEdge (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right (some c)) =
      occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right' (some c) := by
    intro c
    have h := GeometricSegmentWalls.FrameIso.targetEdge_map_of_agreeOffColumn fi hAgree
      ((W4StarParity.columnEquiv w).symm (some c))
    change fi.datum.targetEdge (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right
        (W4StarParity.columnEquiv w ((W4StarParity.columnEquiv w).symm (some c)))) =
      occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right'
        (W4StarParity.columnEquiv w ((W4StarParity.columnEquiv w).symm (some c))) at h
    simpa only [Equiv.apply_symm_apply] using h
  have hNew := StarCensusEngine.frameIso_newEdge hRetained hRetained' fi
  have hEndsNew := fi.datum.ends (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right none)
  rw [hNew] at hEndsNew
  simp only [occurrenceEquiv_none, newEnds] at hEndsNew
  have hEnds : ∀ c : (w.frame.limitTarget w.column).edges, UnorderedEnds fi.datum.targetVertex (oldEnds (w.frame.limitTarget w.column) (mergeVertex w) right c)
      (oldEnds (w.frame.limitTarget w.column) (mergeVertex w) right' c) := by
    intro c
    have h := fi.datum.ends (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right (some c))
    rw [hCol c] at h
    simpa only [occurrenceEquiv_some] using h
  rcases hEndsNew with h | h
  · -- the two expanded wall vertices are fixed
    have hOld : fi.datum.targetVertex (oldVertex (w.frame.limitTarget w.column) (mergeVertex w)) = oldVertex (w.frame.limitTarget w.column) (mergeVertex w) :=
      (congrArg Prod.fst h).symm
    have hFresh : fi.datum.targetVertex (freshVertex (w.frame.limitTarget w.column)) = freshVertex (w.frame.limitTarget w.column) :=
      (congrArg Prod.snd h).symm
    left
    intro e he
    have hInc : (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 = mergeVertex w ∨ (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 = mergeVertex w :=
      (mem_incidentEdges_iff _ _).mp he
    cases hR : right e with
    | false =>
      have hx := (oldEnds_incident_oldVertex_iff (w.frame.limitTarget w.column) (mergeVertex w) right e).mpr ⟨hInc, hR⟩
      have hy' := unorderedEnds_mem (hEnds e) hx
      rw [hOld] at hy'
      exact ((oldEnds_incident_oldVertex_iff (w.frame.limitTarget w.column) (mergeVertex w) right' e).mp hy').2
    | true =>
      have hx := (oldEnds_incident_freshVertex_iff (w.frame.limitTarget w.column) (mergeVertex w) right e).mpr ⟨hInc, hR⟩
      have hy' := unorderedEnds_mem (hEnds e) hx
      rw [hFresh] at hy'
      exact ((oldEnds_incident_freshVertex_iff (w.frame.limitTarget w.column) (mergeVertex w) right' e).mp hy').2
  · -- the two expanded wall vertices are exchanged
    have hOld : fi.datum.targetVertex (oldVertex (w.frame.limitTarget w.column) (mergeVertex w)) = freshVertex (w.frame.limitTarget w.column) :=
      (congrArg Prod.snd h).symm
    have hFresh : fi.datum.targetVertex (freshVertex (w.frame.limitTarget w.column)) = oldVertex (w.frame.limitTarget w.column) (mergeVertex w) :=
      (congrArg Prod.fst h).symm
    right
    intro e he
    have hInc : (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 = mergeVertex w ∨ (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 = mergeVertex w :=
      (mem_incidentEdges_iff _ _).mp he
    cases hR : right e with
    | false =>
      have hx := (oldEnds_incident_oldVertex_iff (w.frame.limitTarget w.column) (mergeVertex w) right e).mpr ⟨hInc, hR⟩
      have hy' := unorderedEnds_mem (hEnds e) hx
      rw [hOld] at hy'
      exact ((oldEnds_incident_freshVertex_iff (w.frame.limitTarget w.column) (mergeVertex w) right' e).mp hy').2
    | true =>
      have hx := (oldEnds_incident_freshVertex_iff (w.frame.limitTarget w.column) (mergeVertex w) right e).mpr ⟨hInc, hR⟩
      have hy' := unorderedEnds_mem (hEnds e) hx
      rw [hFresh] at hy'
      exact ((oldEnds_incident_oldVertex_iff (w.frame.limitTarget w.column) (mergeVertex w) right' e).mp hy').2

end Side

/-- Two members isolating different wall directions `X`, `Y` (with a third direction `Z`)
violate the side dichotomy. -/
theorem false_of_side_rightOf {target : CFGraph} {wall : target.V}
    {X Y Z : target.edges} (hX : X ∈ GluingDatum.incidentEdges wall)
    (hZ : Z ∈ GluingDatum.incidentEdges wall) (hXY : X ≠ Y) (hZX : Z ≠ X) (hZY : Z ≠ Y)
    (h : (∀ e ∈ GluingDatum.incidentEdges wall,
        W3Nd2SourceCandidates.rightOf Y e = W3Nd2SourceCandidates.rightOf X e) ∨
      (∀ e ∈ GluingDatum.incidentEdges wall,
        W3Nd2SourceCandidates.rightOf Y e = !W3Nd2SourceCandidates.rightOf X e)) : False := by
  rcases h with h | h
  · have := h X hX
    simp [W3Nd2SourceCandidates.rightOf, hXY] at this
  · have := h Z hZ
    simp [W3Nd2SourceCandidates.rightOf, hZX, hZY] at this

/-- The regrown-column arithmetic separating `M⁽¹⁾` from `M⁽²⁾`. -/
theorem false_of_selected_eq {α : Type*} [DecidableEq α] (G O L : α) {k₂ k₃ m : ℕ}
    (hk₂ : 0 < k₂) (hk₃ : 0 < k₃) (hm : m + 1 = k₂ + k₃)
    (h : ∀ r : α, ((if r = G then (1 : ℚ) / k₂ else 0) + (if r = O then (1 : ℚ) / k₃ else 0)) =
      (if r = L then (1 : ℚ) / m else 0)) : False := by
  have hk₂' : (0 : ℚ) < k₂ := by exact_mod_cast hk₂
  have hk₃' : (0 : ℚ) < k₃ := by exact_mod_cast hk₃
  have hm' : (m : ℚ) + 1 = k₂ + k₃ := by exact_mod_cast hm
  have hG := h G
  have hO := h O
  by_cases hGL : G = L
  · subst hGL
    by_cases hOG : O = G
    · subst hOG
      simp only [if_true] at hG
      have hmpos : (0 : ℚ) < m := by
        have : (1 : ℚ) ≤ k₃ := by exact_mod_cast hk₃
        linarith
      have hle : (k₂ : ℚ) ≤ m := by
        have : (1 : ℚ) ≤ k₃ := by exact_mod_cast hk₃
        linarith
      have h1 : (1 : ℚ) / m ≤ 1 / k₂ := one_div_le_one_div_of_le hk₂' hle
      have h2 : (0 : ℚ) < 1 / k₃ := by positivity
      linarith
    · simp only [if_neg hOG, if_true, zero_add] at hO
      have h2 : (0 : ℚ) < 1 / k₃ := by positivity
      linarith
  · simp only [if_true, if_neg hGL] at hG
    have h1 : (0 : ℚ) < 1 / k₂ := by positivity
    have h3 : (0 : ℚ) ≤ (if G = O then (1 : ℚ) / k₃ else 0) := by
      split_ifs <;> positivity
    linarith

namespace Setup

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (S : Setup w) (hy : Nondegenerate y)

/-- The wall direction each member isolates on its own side of the regrown edge: `t₄` for
`M⁽¹⁾` and `M⁽²⁾`, `t₂` for `M⁽³⁾`, `t₃` for `M⁽⁴⁾`. -/
noncomputable def isolated : Fin 4 → (w.frame.limitTarget w.column).edges :=
  ![S.geometry.largestTarget, S.geometry.largestTarget, S.geometry.growTarget,
    S.geometry.otherTarget]

theorem right_eq : ∀ i : Fin 4,
    (S.cd i).rowData.candidate.right = W3Nd2SourceCandidates.rightOf (S.isolated i)
  | ⟨0, _⟩ => by
    change W3Nd2SourceCandidates.rightOf S.positionOne.toFourStarGeometry.largestTarget = _
    rw [S.largestOne]
    rfl
  | ⟨1, _⟩ => by
    change W3Nd2SourceCandidates.rightOf S.positionTwo.toFourStarGeometry.largestTarget = _
    rw [S.largestTwo]
    rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

/-- **The side dichotomy between two positions of one class.** -/
theorem side_of_frameIso {i j : Fin 4} {hi : S.Nonsingular i} {hj : S.Nonsingular j}
    (fi : GeometricSegmentWalls.FrameIso (S.rep hy i hi).member.frame
      (S.rep hy j hj).member.frame) :
    (∀ e ∈ GluingDatum.incidentEdges (mergeVertex w),
        W3Nd2SourceCandidates.rightOf (S.isolated j) e =
          W3Nd2SourceCandidates.rightOf (S.isolated i) e) ∨
      (∀ e ∈ GluingDatum.incidentEdges (mergeVertex w),
        W3Nd2SourceCandidates.rightOf (S.isolated j) e =
          !W3Nd2SourceCandidates.rightOf (S.isolated i) e) := by
  rw [← S.right_eq i, ← S.right_eq j]
  exact frameIso_side (hy := hy) ((S.anchor i).retained (S.cd i))
    ((S.anchor j).retained (S.cd j)) fi

/-- Positions isolating different wall directions are never frame isomorphic. -/
theorem not_rel_of_isolated_ne {i j : Fin 4} (hi : S.Nonsingular i) (hj : S.Nonsingular j)
    (hne : S.isolated i ≠ S.isolated j) (Z : (w.frame.limitTarget w.column).edges)
    (hZ : Z ∈ GluingDatum.incidentEdges (mergeVertex w))
    (hZi : Z ≠ S.isolated i) (hZj : Z ≠ S.isolated j)
    (hIncident : S.isolated i ∈ GluingDatum.incidentEdges (mergeVertex w)) :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (S.rep hy i hi).member.frame
      (S.rep hy j hj).member.frame) := by
  rintro ⟨fi⟩
  exact false_of_side_rightOf hIncident hZ hne hZi hZj (S.side_of_frameIso hy fi)

/-- A position's regrown column, read at the limit's rows, is its presented one. -/
theorem matrix_none_presented (i : Fin 4) (r : Option (w.frame.limitTarget w.column).edges) :
    StableSourceMatrix.matrix (S.cd i).rowData.candidate.datum
        (((S.anchor i).E (S.cd i)).row (S.lab.row.symm r))
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w)
          (S.cd i).rowData.candidate.right none) =
      GluingDatum.LengthMatrixPresentation.matrix (S.receipts.presentation i) r none := by
  rw [GaugeAnchor.E_row, S.presentation_eq i]
  exact (ColumnData.presented_matrix_none (S.cd i) r).symm

/-- **`M⁽¹⁾` and `M⁽²⁾` are never frame isomorphic**: their regrown columns differ. -/
theorem not_rel_01 (h0 : S.Nonsingular 0) (h1 : S.Nonsingular 1) :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (S.rep hy 0 h0).member.frame
      (S.rep hy 1 h1).member.frame) := by
  classical
  rintro ⟨fi⟩
  have hSel : ∀ r, MemberColumn.selectedNewSum S.receipts.member 0 r =
      MemberColumn.selectedNewSum S.receipts.member 1 r := by
    intro r
    have hNew := StarCensusEngine.frameIso_matrix_new ((S.anchor 0).retained (S.cd 0))
      ((S.anchor 1).retained (S.cd 1)) fi (S.lab.row.symm r)
    rw [S.matrix_none_presented 0 r, S.matrix_none_presented 1 r] at hNew
    have e0 := MemberColumn.matrix_none_eq S.receipts.member S.receipts.rows.oldPath 0 r
    have e1 := MemberColumn.matrix_none_eq S.receipts.member S.receipts.rows.oldPath 1 r
    change GluingDatum.LengthMatrixPresentation.matrix (S.receipts.presentation 0) r none = _ at e0
    change GluingDatum.LengthMatrixPresentation.matrix (S.receipts.presentation 1) r none = _ at e1
    rw [S.receipts.background_one] at e0
    rw [S.receipts.background_two] at e1
    linarith
  apply false_of_selected_eq S.receipts.rows.rowGrow S.receipts.rows.rowOther
    S.receipts.rows.rowLargest
    ((w.limit.edgePartition S.geometry.growTarget).blockCard_pos S.geometry.growAnchor)
    ((w.limit.edgePartition S.geometry.otherTarget).blockCard_pos S.geometry.otherAnchor)
    S.receipts.index_two
  intro r
  have h := hSel r
  unfold MemberColumn.selectedNewSum at h
  rw [S.receipts.selected_one, S.receipts.selected_two] at h
  simp only [List.map_append, List.sum_append, single_map_sum] at h
  rw [S.receipts.index_one_grow, S.receipts.index_one_other] at h
  exact h

/-- **Distinct nonsingular positions are distinct star classes** (Stage 3). -/
theorem rep_eq_of_cls_eq (i : Fin 4) (hi : S.Nonsingular i) (j : Fin 4) (hj : S.Nonsingular j)
    (h : (S.rep hy i hi).cls = (S.rep hy j hj).cls) : i = j := by
  have hRel : Nonempty (GeometricSegmentWalls.FrameIso (S.rep hy i hi).member.frame
      (S.rep hy j hj).member.frame) := Quotient.exact h
  have hRel' : Nonempty (GeometricSegmentWalls.FrameIso (S.rep hy j hj).member.frame
      (S.rep hy i hi).member.frame) := hRel.elim fun fi ↦ ⟨fi.symm⟩
  have hGO := S.geometry.grow_ne_other
  have hGL := S.geometry.grow_ne_largest
  have hOL := S.geometry.other_ne_largest
  have mG := S.geometry.growTarget_mem
  have mO := S.geometry.otherTarget_mem
  have mL := S.geometry.largestTarget_mem
  fin_cases i <;> fin_cases j
  · rfl
  · exact (S.not_rel_01 hy hi hj hRel).elim
  · exact (S.not_rel_of_isolated_ne hy hi hj hGL.symm _ mO hOL hGO.symm mL hRel).elim
  · exact (S.not_rel_of_isolated_ne hy hi hj hOL.symm _ mG hGL hGO mL hRel).elim
  · exact (S.not_rel_01 hy hj hi hRel').elim
  · rfl
  · exact (S.not_rel_of_isolated_ne hy hi hj hGL.symm _ mO hOL hGO.symm mL hRel).elim
  · exact (S.not_rel_of_isolated_ne hy hi hj hOL.symm _ mG hGL hGO mL hRel).elim
  · exact (S.not_rel_of_isolated_ne hy hi hj hGL _ mO hGO.symm hOL mG hRel).elim
  · exact (S.not_rel_of_isolated_ne hy hi hj hGL _ mO hGO.symm hOL mG hRel).elim
  · rfl
  · exact (S.not_rel_of_isolated_ne hy hi hj hGO _ mL hGL.symm hOL.symm mG hRel).elim
  · exact (S.not_rel_of_isolated_ne hy hi hj hOL _ mG hGO hGL mO hRel).elim
  · exact (S.not_rel_of_isolated_ne hy hi hj hOL _ mG hGO hGL mO hRel).elim
  · exact (S.not_rel_of_isolated_ne hy hi hj hGO.symm _ mL hOL.symm hGL.symm mO hRel).elim
  · rfl

end Setup

/-! ## 5.  The census at one wall -/

namespace Setup

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (S : Setup w) (hy : Nondegenerate y)

/-- The positions' classes, as a map from the nonsingular positions to the star. -/
noncomputable def repCls (i : {i : Fin 4 // S.Nonsingular i}) : GeometricStar.Star hy w :=
  (S.rep hy i.1 i.2).cls

theorem repCls_injective : Function.Injective (S.repCls hy) :=
  fun a b h ↦ Subtype.ext (S.rep_eq_of_cls_eq hy a.1 a.2 b.1 b.2 h)

/-- **The exhaustion residue at one wall** (Stage 2 (b)): every member of the star is in
the class of some nonsingular position.  *Interface*: equivalent to the census at this
wall (`census_of_exhaustion`, `exhaustion_of_census`) and to the star having exactly as
many classes as Equation (2) has nonsingular positions (`exhausts_iff_card`). -/
def Exhausts : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ i : Fin 4, ∃ hi : S.Nonsingular i,
    member.cls = (S.rep hy i hi).cls

/-- **The W3Four census at one wall from exhaustion.** -/
theorem census_of_exhaustion (hExh : S.Exhausts hy) :
    ∃ e : {i : Fin 4 // S.Nonsingular i} ≃ GeometricStar.Star hy w,
      ∀ i, (GeometricStar.Star.toFibre (e i)).multNat =
        (signedMult (S.receipts.presentation i.1)).num.natAbs := by
  refine ⟨Equiv.ofBijective _ ⟨S.repCls_injective hy, ?_⟩,
    fun i ↦ S.multNat_rep hy i.1 i.2⟩
  refine Quotient.ind ?_
  intro member
  obtain ⟨i, hi, h⟩ := hExh member
  exact ⟨⟨i, hi⟩, h.symm⟩

/-- **Interface: the census implies exhaustion.** -/
theorem exhaustion_of_census (e : {i : Fin 4 // S.Nonsingular i} ≃ GeometricStar.Star hy w) :
    S.Exhausts hy := by
  classical
  have hBij : Function.Bijective (S.repCls hy) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨S.repCls_injective hy, Fintype.card_congr e⟩
  intro member
  obtain ⟨i, hi⟩ := hBij.2 member.cls
  exact ⟨i.1, i.2, hi.symm⟩

/-- **Stages 1 and 3 inject the nonsingular positions into the star**, unconditionally. -/
theorem card_nonsingular_le :
    Nat.card {i : Fin 4 // S.Nonsingular i} ≤ Nat.card (GeometricStar.Star hy w) :=
  Nat.card_le_card_of_injective _ (S.repCls_injective hy)

/-- **The census at one wall is a count**: exhaustion holds exactly when the star has as
many classes as Equation (2) has nonsingular positions. -/
theorem exhausts_iff_card :
    S.Exhausts hy ↔
      Nat.card (GeometricStar.Star hy w) = Nat.card {i : Fin 4 // S.Nonsingular i} := by
  classical
  constructor
  · intro hExh
    obtain ⟨e, -⟩ := S.census_of_exhaustion hy hExh
    exact (Nat.card_congr e).symm
  · intro hCard
    refine S.exhaustion_of_census hy (Fintype.equivOfCardEq ?_)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hCard]

include hy in
/-- **Equation (2) never has exactly one nonsingular position**: its terms are integers
summing to zero, and a nonsingular term is nonzero. -/
theorem card_nonsingular_ne_one : Nat.card {i : Fin 4 // S.Nonsingular i} ≠ 1 := by
  classical
  intro h1
  rw [Nat.card_eq_one_iff_exists] at h1
  obtain ⟨⟨i, hi⟩, hUnique⟩ := h1
  have hSum := S.sum_signedMult hy
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hSum
  have hRest : ∑ j ∈ Finset.univ.erase i, signedMult (S.receipts.presentation j) = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ S.signedMult_eq_zero j fun hjs ↦ ?_
    have := hUnique ⟨j, hjs⟩
    exact (Finset.mem_erase.mp hj).1 (congrArg Subtype.val this)
  rw [hRest, add_zero] at hSum
  have hAbs : absMult (S.receipts.presentation i) ≠ 0 := (absMult_ne_zero_iff _).mpr hi
  exact hAbs (by unfold absMult; rw [hSum, abs_zero])

/-- **The star clause at one wall from exhaustion.** -/
theorem starParityAt_of_exhaustion (hExh : S.Exhausts hy) :
    RegrowthWallInput.StarParityAt hy w := by
  obtain ⟨e, hmult⟩ := S.census_of_exhaustion hy hExh
  exact StarCensusEngine.starParityAt_of_census
    (fun i ↦ signedMult (S.receipts.presentation i)) (S.integral_signedMult hy)
    (S.sum_signedMult hy) S.Nonsingular S.signedMult_eq_zero e hmult

end Setup

/-! ## 6.  The family clause -/

section Family

open ClassifiedContinuation (SourceCase)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Every `w3Four` regrowth carries a setup**: the classification's `four` constructor,
the far endpoint of `t₃` as root (as in `RegrowthBalances.exists_w3Four_balance`), and
Part I's two gauge moves (`W3FourClosure.exists_member_one`/`_two`). -/
theorem exists_setup (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w3Four) : Nonempty (Setup w) := by
  have hConnected := RegrowthBalances.limit_connected w
  have hGenus := RegrowthBalances.limit_genus w
  cases cls with
  | w4 => cases htag
  | w2 _ _ profile => cases profile <;> cases htag
  | w3 star input classification =>
    cases classification with
    | shift => cases htag
    | nd3CoarseFine => cases htag
    | nd2CoarseFine => cases htag
    | four profile directions largest_index pair_index =>
      have hOtherIncident :=
        (mem_incidentEdges_iff _ _).mp
          (growProfileFirst profile directions largest_index).otherTarget_mem
      have hGrowIncident :=
        (mem_incidentEdges_iff _ _).mp
          (growProfileFirst profile directions largest_index).growTarget_mem
      have hLargestIncident :=
        (mem_incidentEdges_iff _ _).mp
          (growProfileFirst profile directions largest_index).largestTarget_mem
      have hRoot := TargetSeparation.farEndpoint_ne hOtherIncident
      have hGrowFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus hOtherIncident
        hGrowIncident
        (Ne.symm (growProfileFirst profile directions largest_index).grow_target_ne_other)
      have hLargestFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus
        hOtherIncident hLargestIncident
        (growProfileFirst profile directions largest_index).other_target_ne_largest
      have hOtherMoved := TargetSeparation.edgeMoved_self_eq_true hOtherIncident
      obtain ⟨permOne, fixOne, positionOne, -, geomOne, -, -, indexOneGrow, indexOneOther⟩ :=
        W3FourClosure.exists_member_one
          (ofGrowProfile (growProfileFirst profile directions largest_index)) _ hRoot
          hGrowFixed hLargestFixed hOtherMoved
      obtain ⟨permTwo, fixTwo, positionTwo, -, geomTwo, -, -, indexTwo⟩ :=
        W3FourClosure.exists_member_two
          (ofGrowProfile (growProfileFirst profile directions largest_index)) _ hRoot
          hGrowFixed hLargestFixed hOtherMoved
      exact ⟨{ star := star, input := input, profile := profile, directions := directions
               largest_index := largest_index, root := _, hRoot := hRoot
               hGrowFixed := hGrowFixed, hLargestFixed := hLargestFixed
               hOtherMoved := hOtherMoved
               permOne := permOne, fixOne := fixOne, positionOne := positionOne
               geomOne := geomOne, indexOneGrow := indexOneGrow
               indexOneOther := indexOneOther
               permTwo := permTwo, fixTwo := fixTwo, positionTwo := positionTwo
               geomTwo := geomTwo, indexTwo := indexTwo }⟩

/-- **The W3Four star census.**  At every regrowth tagged `w3Four`, for every setup of
Figure 28's family, the star is in bijection with the family's nonsingular positions, each
class carrying its position's term of Equation (2).  *Interface*: equivalent to
`W3FourStarExhaustion` (`w3FourStarExhaustion_iff`). -/
def W3FourStarCensus (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Four →
    ∀ S : Setup w,
      ∃ e : {i : Fin 4 // S.Nonsingular i} ≃ GeometricStar.Star hy w,
        ∀ i, (GeometricStar.Star.toFibre (e i)).multNat =
          (signedMult (S.receipts.presentation i.1)).num.natAbs

/-- **`FamilyStarParity … .w3Four` from the census**: Equation (2) at a setup (which every
`w3Four` regrowth carries, `exists_setup`) read mod two through the engine. -/
theorem familyStarParity_w3Four_of_census (h : W3FourStarCensus degree n p) :
    RegrowthWallInput.FamilyStarParity degree n p .w3Four := by
  intro core y hy w cls htag
  obtain ⟨S⟩ := exists_setup w cls htag
  obtain ⟨e, hmult⟩ := h core y hy w cls htag S
  exact StarCensusEngine.starParityAt_of_census
    (fun i ↦ signedMult (S.receipts.presentation i)) (S.integral_signedMult hy)
    (S.sum_signedMult hy) S.Nonsingular S.signedMult_eq_zero e hmult

/-- **Stage 2's residue, family-wide**: at every `w3Four` regrowth, for every setup, every
star member is in the class of a nonsingular position.  *Interface*: equivalent to
`W3FourStarCensus` (`w3FourStarExhaustion_iff`) and to `W3FourStarCard`
(`w3FourStarExhaustion_iff_card`). -/
def W3FourStarExhaustion (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Four → ∀ S : Setup w, S.Exhausts hy

theorem w3FourStarCensus_of_exhaustion (hExh : W3FourStarExhaustion degree n p) :
    W3FourStarCensus degree n p :=
  fun core y hy w cls htag S ↦ S.census_of_exhaustion hy (hExh core y hy w cls htag S)

theorem exhaustion_of_w3FourStarCensus (hCensus : W3FourStarCensus degree n p) :
    W3FourStarExhaustion degree n p :=
  fun core y hy w cls htag S ↦
    S.exhaustion_of_census hy (hCensus core y hy w cls htag S).choose

theorem w3FourStarExhaustion_iff :
    W3FourStarExhaustion degree n p ↔ W3FourStarCensus degree n p :=
  ⟨w3FourStarCensus_of_exhaustion, exhaustion_of_w3FourStarCensus⟩

/-- **The residue, as a count**: at every `w3Four` regrowth and setup the star has exactly
as many classes as Equation (2) has nonsingular positions.  *Interface*: equivalent to
`W3FourStarExhaustion` (`w3FourStarExhaustion_iff_card`). -/
def W3FourStarCard (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Four → ∀ S : Setup w,
      Nat.card (GeometricStar.Star hy w) = Nat.card {i : Fin 4 // S.Nonsingular i}

theorem w3FourStarExhaustion_iff_card :
    W3FourStarExhaustion degree n p ↔ W3FourStarCard degree n p :=
  ⟨fun h core y hy w cls htag S ↦ (S.exhausts_iff_card hy).mp (h core y hy w cls htag S),
    fun h core y hy w cls htag S ↦ (S.exhausts_iff_card hy).mpr (h core y hy w cls htag S)⟩

/-- **The `w3Four` clause of `FamilyStarParity`** at genus six and degree four, modulo
Stage 2's exhaustion alone. -/
theorem familyStarParity_w3Four_of_exhaustion
    (hExh : W3FourStarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w3Four :=
  familyStarParity_w3Four_of_census (w3FourStarCensus_of_exhaustion hExh)

end Family

/-! ## 7.  Stage 2 reduced to decoupled transports onto the four anchored positions -/

section Transport

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (hy : Nondegenerate y)
  {geometry : FourStarGeometry w.limit (mergeVertex w)} {labelling : StablePathLabelling w.limit}
  (cd : ColumnData w.limit (mergeVertex w) geometry labelling) (A : GaugeAnchor w cd)

/-- **A member receiving a decoupled transport onto a gauged position is in its class**:
`StarCensusEngine.cls_eq_of_transport` at the position's anchor (the gauge copy, carried
back by `A.φ`), the member normalized at a placement of its choice
(`W3Nd2StarCensusProof.memberNorm`, valency-free). -/
theorem GaugeAnchor.cls_eq_of_transport
    (fd : FullDimensionalSourcePresentation cd.rowData.candidate.datum (Fin p))
    (member : GeometricStar.StarMember hy w) (ψ : GeometricStar.LimitIso hy member.member w)
    (placement : (member.member.frame.limitTarget member.member.column).edges → Bool)
    (hPlacement : W3Nd2StarCensusProof.PlacementSpec member.member placement)
    (t : ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
      (mergeVertex member.member) (mergeVertex w) placement cd.rowData.candidate.right
      (W3Nd2StarCensusProof.memberResolution member.member placement hPlacement)
      (M11StarCensusProof.pasted cd.rowData.candidate)) :
    member.cls = (GaugeAnchor.member hy cd A fd).cls := by
  have hNV := M11WallExhaustion.sourceVertexMap_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  have hNE := M11WallExhaustion.retainedSourceEdge_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
    (E := A.E cd) (fd := fd) (hRetained := A.retained cd) (M := cd.base) (φ := A.φ)
    (hMerge := gaugedMerge cd) (hOld := M11StarCensusProof.candidate_old _)
    (hEdge := M11StarCensusProof.candidate_edge _) (A.branchSquare cd) (A.rowSquare cd)
    (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _ cd.rowData.candidate.exterior)
    rfl member ψ (W3Nd2StarCensusProof.memberNorm member.member placement hPlacement)
    hNV hNE t

end Transport

namespace Setup

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (S : Setup w) (hy : Nondegenerate y)

/-- **The receipt a member must present to be received at position `i`**: a decoupled
transport, along its limit isomorphism followed by the position's inverse anchor (the
inverse branch swap at `M⁽¹⁾`, `M⁽²⁾`; the identity at `M⁽³⁾`, `M⁽⁴⁾`), from its own normal
form at some placement onto the position's pasted resolution. -/
def PositionTransport (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : W3Nd2StarCensusProof.PlacementSpec other placement) (i : Fin 4) : Type :=
  ResolutionExpansionFree.TransportFree (ψ.datum.trans (S.anchor i).φ.symm)
    (mergeVertex other) (mergeVertex w) placement (S.cd i).rowData.candidate.right
    (W3Nd2StarCensusProof.memberResolution other placement hPlacement)
    (M11StarCensusProof.pasted (S.cd i).rowData.candidate)

/-- **Stage 2 reduced to transports**: if every star member presents a decoupled transport
onto a nonsingular position of Equation (2), the star is exhausted by the positions. -/
theorem exhausts_of_transports
    (h : ∀ member : GeometricStar.StarMember hy w,
      ∃ ψ : GeometricStar.LimitIso hy member.member w,
      ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
      ∃ hPlacement : W3Nd2StarCensusProof.PlacementSpec member.member placement,
      ∃ i : Fin 4, ∃ _ : S.Nonsingular i,
        Nonempty (S.PositionTransport hy member.member ψ placement hPlacement i)) :
    S.Exhausts hy := by
  intro member
  obtain ⟨ψ, placement, hPlacement, i, hi, ⟨t⟩⟩ := h member
  exact ⟨i, hi, GaugeAnchor.cls_eq_of_transport hy (S.cd i) (S.anchor i) (S.fdAt hy i hi)
    member ψ placement hPlacement t⟩

end Setup

/-! ## 8.  Which positions are singular (inference (i) of the module docstring, in Lean)

Figure 28's four determinants (`W3FourStableGraph.Figure28Receipts.det_one` … `det_four`)
say exactly when each position is singular: `M⁽²⁾`, `M⁽³⁾`, `M⁽⁴⁾` exactly when the cofactor
`c(e₄)`, `c(e₂)`, `c(e₃)` of their displayed row vanishes, `M⁽¹⁾` exactly when
`c(e₂)/k₂ + c(e₃)/k₃ = c(e₄)/k₄`. -/

namespace Setup

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (S : Setup w)

theorem indexGrow_pos : (0 : ℚ) < (indexGrow S.geometry : ℚ) := by
  exact_mod_cast (w.limit.edgePartition S.geometry.growTarget).blockCard_pos S.geometry.growAnchor

theorem indexOther_pos : (0 : ℚ) < (indexOther S.geometry : ℚ) := by
  exact_mod_cast
    (w.limit.edgePartition S.geometry.otherTarget).blockCard_pos S.geometry.otherAnchor

theorem nonsingular_zero_iff : S.Nonsingular 0 ↔
    (1 : ℚ) / (indexGrow S.geometry : ℚ) * S.receipts.cTwo +
        (1 : ℚ) / (indexOther S.geometry : ℚ) * S.receipts.cThree -
        (1 : ℚ) / (indexLargest S.geometry : ℚ) * S.receipts.cFour ≠ 0 := by
  unfold Nonsingular
  rw [S.receipts.det_one]

theorem nonsingular_one_iff : S.Nonsingular 1 ↔ S.receipts.cFour ≠ 0 := by
  unfold Nonsingular
  rw [S.receipts.det_two, indexLargest_eq]
  have h2 : (1 : ℚ) ≤ indexGrow S.geometry := by
    exact_mod_cast (w.limit.edgePartition S.geometry.growTarget).blockCard_pos S.geometry.growAnchor
  have h3 : (1 : ℚ) ≤ indexOther S.geometry := by
    exact_mod_cast
      (w.limit.edgePartition S.geometry.otherTarget).blockCard_pos S.geometry.otherAnchor
  push_cast
  set a : ℚ := (indexGrow S.geometry : ℚ) + (indexOther S.geometry : ℚ)
  have ha : (2 : ℚ) ≤ a := by simp only [a]; linarith
  have hFactor : (1 : ℚ) / (a - 1) - 1 / a ≠ 0 := by
    have ha1 : a - 1 ≠ 0 := by linarith
    have ha0 : a ≠ 0 := by linarith
    rw [div_sub_div _ _ ha1 ha0]
    exact div_ne_zero (by ring_nf; norm_num) (mul_ne_zero ha1 ha0)
  constructor
  · intro h hc
    exact h (by rw [hc]; ring)
  · intro hc h
    have : ((1 : ℚ) / (a - 1) - 1 / a) * S.receipts.cFour = 0 := by rw [← h]; ring
    exact (mul_ne_zero hFactor hc) this

theorem nonsingular_two_iff : S.Nonsingular 2 ↔ S.receipts.cTwo ≠ 0 := by
  unfold Nonsingular
  rw [S.receipts.det_three]
  have hk := S.indexGrow_pos
  set k : ℚ := (indexGrow S.geometry : ℚ)
  have hFactor : (1 : ℚ) / (k + 1) - 1 / k ≠ 0 := by
    have hk1 : k + 1 ≠ 0 := by linarith
    rw [div_sub_div _ _ hk1 hk.ne']
    exact div_ne_zero (by ring_nf; norm_num) (mul_ne_zero hk1 hk.ne')
  constructor
  · intro h hc
    exact h (by rw [hc]; ring)
  · intro hc h
    have : ((1 : ℚ) / (k + 1) - 1 / k) * S.receipts.cTwo = 0 := by rw [← h]; ring
    exact (mul_ne_zero hFactor hc) this

theorem nonsingular_three_iff : S.Nonsingular 3 ↔ S.receipts.cThree ≠ 0 := by
  unfold Nonsingular
  rw [S.receipts.det_four]
  have hk := S.indexOther_pos
  set k : ℚ := (indexOther S.geometry : ℚ)
  have hFactor : (1 : ℚ) / (k + 1) - 1 / k ≠ 0 := by
    have hk1 : k + 1 ≠ 0 := by linarith
    rw [div_sub_div _ _ hk1 hk.ne']
    exact div_ne_zero (by ring_nf; norm_num) (mul_ne_zero hk1 hk.ne')
  constructor
  · intro h hc
    exact h (by rw [hc]; ring)
  · intro hc h
    have : ((1 : ℚ) / (k + 1) - 1 / k) * S.receipts.cThree = 0 := by rw [← h]; ring
    exact (mul_ne_zero hFactor hc) this

end Setup

end DraismaVargas.Count.W3FourStarCensusProof
