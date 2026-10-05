module

public import DraismaVargas.LocalCases.InteriorBridgesAll
public import DraismaVargasCount.W4WallExhaustion
public import DraismaVargasCount.SimpleWallSupply
public import DraismaVargasCount.InheritedLimitBranches
public import DraismaVargasCount.W3Nd3UnitBalance
public import DraismaVargasCount.W3Nd2UnitBalance
public import DraismaVargasCount.W2R1UnitBalance
public import DraismaVargasCount.W2PMultiplicityBalance
public import DraismaVargasCount.W4FullDimensionalBalance

@[expose] public section

/-!
# From a `Regrowth` to Part I's wall objects

The trivalent-wall step of the count (step 2 of `DraismaVargasCount.Assembly`) is proved one wall
type at a time.  This module connects the walls of the count to the classification of interior
walls in J. Draisma and A. Vargas, *Catalan-many tropical morphisms to trees; Part I:
Constructions*, arXiv:1909.12924 -- its ten-way interior classification
(`LocalCases.IncomingSourceCases`) and its wall dispatcher (`LocalCases.InteriorProgress`,
`LocalCases.InteriorBridgesAll`) -- so that Part I's balancing identities (Equations (1)--(10) of
its section "Constructions") can be applied at the limit of a regrowth.  In Vargas, Part II
(arXiv:2609.09109) these enter through the star of a codimension-one limit and the balancing
condition `prop-signed-mult`.

## Regrowths are interior walls

A `WallStar.Regrowth` over a positive request is **not** Part I's facet arrival
(`OuterWalk.FacetArrival`/`WallData`): those are *type-change* walls, where a stable
row vanishes (`WallData.hFacetZero`), and a regrowth's stable rows are the requested
slot lengths, all positive (`not_wallData`).  It **is** Part I's *interior* wall: its
own coordinates are an `InteriorProgress.AdmissibleColumn` metric at its column
(`admissibleColumn`), and its limit is *definitionally* the contracted wall datum the
interior classifier reads (`limit_eq_contractDatum`, `rfl`).  Part I's interior
classification and its per-wall producer are both stated at an **arbitrary**
full-dimensional cover and column -- no march, no `FacetArrival`, no `TrackedState`
enters: `InteriorProgress.nonempty_classification_of_admissibleColumn` classifies from
`(fullDim, column, AdmissibleColumn)` alone, and `InteriorBridgesAll.wallBridge`
produces a tracked routed wall from those plus the chart equation (`rfl` here) and a
`Tracks`, which every presentation supplies of itself
(`InteriorGraphTracking.Tracks.self`).  So the adapter needs **no new data**, and the
classification it produces lands, with no further input, in the binders of the
balancing identities (§6).

## Main results

* §1 `rowLength_pos`, `admissibleColumn` -- the regrowth's coordinates are Part I's
  interior wall metric.  `not_wallData` -- no facet arrival's wall data has a regrowth's
  matrix and coordinates.
* §2 `limit_eq_contractDatum`, `mergeVertex_eq` -- the limit and its merged vertex
  are, by `rfl`, the classifier's wall datum and wall vertex.
* §3 `nonempty_classification`, `classification`, `sourceCase` -- the ten-way
  classification of `w.limit` at `W4WallExhaustion.mergeVertex w`, whose constructors
  carry the family inputs the balancing identities take (`AuxR0SourceInput`;
  `W3SourceInput` + profile; `W2SourceInput` + profile).  `tagValency`,
  `card_incidentEdges_eq_tagValency`, `sourceCase_eq_w4_iff` -- **the wall valency
  pins the valency class of the tag**, for every classification; in particular a
  four-valent wall classifies as `w4` and nothing else (`sourceCase_eq_w4`), and every
  regrowth's wall has valency two, three or four (`card_incidentEdges_mem`).
* §4 `nonempty_trackedRoutedWall`, `nonempty_routedWall`, `exists_wallInput` -- a
  (tracked) routed wall at the regrowth's column, for all ten tags, with an incoming
  member presenting the regrowth's own matrix.
* §5 the **faithful** W4 route: `w4Input`, `w4Classification`, `w4Incoming`,
  `exists_w4Matched`, `w4Matched`, `w4Routed`, `w4WallInput` and the equations
  `w4Routed_case`, `w4Routed_target`, `w4Routed_data`, `w4Routed_wallVertex`,
  `w4Routed_incoming` -- the wall input's datum *is* `w.limit`, its tag *is* `w4`, and
  its incoming member *is* Part I's pairing index of the regrowth's own cover
  (`W4IncomingTargetNormalization.pairing`).
* §6 the balancing identities at the regrowth's limit: `w4_sum_signedMult_eq_zero` --
  **Equation (1) at every four-valent regrowth**, `W4FullDimensionalBalance`'s one
  extra datum (an incoming full-dimensional member) being the regrowth's own matched
  cover; `exists_w3Nd3_balance`, `exists_w3Nd2_balance`, `exists_w2R1_balance` -- the
  three hypothesis-free balances, fed by the classification's own payload;
  `exists_w2P_balance` -- Equation (9), whose incoming member is the regrowth's own
  cover matched by Part I.
* §7 `StarParityAt`, `FamilyStarParity`, `starParityAt_of_family`,
  `familyStarParity_iff`, `inConeSupplySimple_of_familyStarParity` -- the per-family
  split of `hstar`, typechecked against `SimpleWallSupply.InConeSupplySimple`.
  `(∀ tag, FamilyStarParity degree n p tag)` is **equivalent** to the `hstars`
  antecedent of `SimpleWallSupply.inConeSupplySimple_of_even_stars`
  (`familyStarParity_iff`).  `StarSupplyAssembly` proves it one tag at a time at genus
  six, and `inConeSupplySimple_of_familyStarParity` turns it into step 2.

## The ten wall types

For each tag: Part I's balancing identity, how Part I identifies an *arbitrary* incoming cover
(the regrowth's own frame) with a member of the family, and the balance in this library.  Each
identification exists at the member's own limit and returns a position, a full-dimensional
presentation of that member with the same matrix and wall column, and a stable-incidence
equivalence, built on a target isomorphism plus a global sheet relabelling.

| tag | Part I | incoming identification | balance |
|---|---|---|---|
| `w4` | Equation (1) | `InteriorGraphTracking.exists_matched_tracking`, over `W4PositiveExit.exists_matchedPresentation`; index `W4IncomingTargetNormalization.pairing` | `W4FullDimensionalBalance.sum_signedMult_eq_zero`; here `w4_sum_signedMult_eq_zero` |
| `w3Four` | Equation (2) | `InteriorBridgesTrivalent.exists_four_matched_tracking_of_classification` | `W3FourCountBalance.exists_sum_signedMult_eq_zero` (root receipts and an incoming member) |
| `w3Shift` | Equation (3) | `InteriorBridgesTrivalent.exists_shift_matched_tracking_of_classification`, via `W3ShiftGraphTracking.exists_matched_tracking` | `W3ShiftMultiplicityBalance.sum_signedMult_eq_zero` (an incoming member) |
| `w3Nd3CoarseFine` | Equation (4) | `W3Nd3GraphTracking.exists_matched_tracking` | `W3Nd3UnitBalance.sum_signedMult_canonical_eq_zero`; here `exists_w3Nd3_balance` |
| `w3Nd2CoarseFine` | Equation (5) | `W3Nd2GraphTracking.exists_matched_tracking` | `W3Nd2UnitBalance.sum_signedMult_canonical_eq_zero`; here `exists_w3Nd2_balance` |
| `w2M11` | Equation (6) | `W2M11GraphTracking.exists_matched_tracking`; payload `exists_w2M11_payload` | `M11IncomingDenominator.sum_signedMult_canonical_eq_zero` (an incoming member) |
| `w2M1k` | Equation (7) | `W2M1kGraphTracking.exists_matched_tracking`; payload `exists_w2M1k_payload`; three bases, `W2M1kClosureUnconditional.headline_cases` | `W2M1kIncomingTame.sum_signedMult_canonical_eq_zero` (an incoming member) |
| `w2Mkk` | Equation (8) | `W2MkkGraphTracking.exists_matched_tracking`; payload `exists_w2Mkk_payload` | `W2MkkIncomingDenominator.sum_signedMult_canonical_eq_zero` (an incoming member and detach data) |
| `w2P` | Equation (9) | `W2PGraphTracking.exists_matched_tracking`; payload `W2PArbitraryIncomingExit.exists_w2P_payload` | `W2PMultiplicityBalance.sum_signedMult_eq_zero`; here `exists_w2P_balance` |
| `w2R1` | Equation (10) | `W2R1GraphTracking.exists_matched_tracking`; payload `W2R1ArbitraryIncomingExit.exists_w2R1_payload` | `W2R1UnitBalance.sum_signedMult_canonical_eq_zero`; here `exists_w2R1_balance` |

The balances for `w3Four`, `w3Shift`, `w2M1k` and `w2Mkk` are composed at the regrowth in
`RegrowthBalances`, and the one for `w2M11` in `M11StarParityFree`; `w2M11`, `w2M1k` and `w2Mkk`
state their balance in `Option` coordinates.

## Remarks

* **The tag within a valency class is not unique.**  The W3 and W2 source-profile
  classifiers are existential (`W3IncomingClassification.exists_classification`,
  `W2IncomingClassification.exists_classification` return `Nonempty`), so at a
  trivalent or divalent wall `sourceCase` is whichever tag the chosen classification
  carries; only its valency class is pinned (`card_incidentEdges_eq_tagValency`).
  `FamilyStarParity` quantifies over *all* classifications, so this is harmless for
  its users.  At a four-valent wall the tag is unique (`sourceCase_eq_w4`).
* **The generic routed wall is not faithful.**  `InteriorBridgesAll.wallBridge`
  returns `Nonempty (TrackedRoutedWall …)`, which forgets that the wall input's datum
  is the contracted datum and that its tag is the classification's.  §5 recovers both
  for `w4` by building the routed wall directly (the `w4Bridge_w4` recipe).  For the other
  nine tags this is not needed: nothing in the count consumes a `WallInput`, and the
  balances consume the classification's payload, which §3 delivers faithfully for all ten
  tags (§6).
* **`hDiscrete` and the three `W4WallExhaustion.Candidate`s are not supplied here.**  The
  adapter supplies `W4WallExhaustion`'s `hFour` (from the tag) and a `FourStar`, and
  §6 proves the balance on the *balance's* family (`W4OutgoingStableRows.member`), not
  on the star's candidates.
* **No march-level statement.**  Nothing here says a count schedule's walls are
  reached by a Part I march; none is needed.
-/

namespace DraismaVargas.Count.RegrowthWallInput

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction
open DraismaVargas.Infrastructure.CubicDarts (CubicDartGraph)
open ClassifiedContinuation (SourceCase)
open W4TargetPairings (FourStar)
open WallStar (Regrowth Nondegenerate)
open SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-! ## 1.  The regrowth's coordinates are Part I's interior wall metric -/

/-- **Every stable row of a regrowth's frame is positive at its own request**: the
frame realizes the request, so its row lengths are the requested slot lengths. -/
theorem rowLength_pos (w : Regrowth core y degree) (hy : Nondegenerate y) (row : Fin p) :
    0 < w.frame.matrix.mulVec (w.frame.coordsAt y) row := by
  rw [w.frame.mulVec_coordsAt y]
  exact hy (w.frame.slot row)

/-- **The adapter's metric.**  A regrowth's own coordinates are a nonnegative chart
point vanishing at its column whose stable rows are all nonzero: Part I's interior wall
metric (`InteriorProgress.AdmissibleColumn`) at the regrowth's column, with no march. -/
theorem admissibleColumn (w : Regrowth core y degree) (hy : Nondegenerate y) :
    InteriorProgress.AdmissibleColumn w.frame.fullDim w.column :=
  ⟨w.frame.coordsAt y, fun c ↦ w.degenerate.closed c, w.degenerate.1,
    fun row ↦ (rowLength_pos w hy row).ne'⟩

/-- **A regrowth is not a facet arrival.**  Part I's `OuterWalk.WallData` is the
payload of a *type-change* wall: its facet row vanishes (`WallData.hFacetZero`).  A
regrowth over a positive request keeps every stable row positive, so no facet arrival's
wall data has a regrowth's matrix and coordinates.  So a regrowth is not a
`FacetArrival`/`WallData`; the Part I object it corresponds to is the interior wall
of `admissibleColumn`. -/
theorem not_wallData {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {graph : CubicDartGraph D V} {label : D → Fin p} {facet : Fin p}
    {arrival : OuterWalk.FacetArrival degree graph label facet}
    (wd : OuterWalk.WallData arrival) (w : Regrowth core y degree) (hy : Nondegenerate y)
    (hMatrix : wd.incomingMatrix = w.frame.matrix)
    (hCoordinates : wd.coordinates = w.frame.coordsAt y) : False := by
  have hZero := wd.hFacetZero
  rw [hMatrix, hCoordinates] at hZero
  exact (rowLength_pos w hy facet).ne' hZero

/-! ## 2.  The limit is the classifier's wall datum, definitionally -/

/-- The limit of a regrowth *is* Part I's contracted wall datum at its column. -/
theorem limit_eq_contractDatum (w : Regrowth core y degree) :
    w.limit = contractDatum w.frame.data (InteriorProgress.hc_column w.frame.fullDim w.column)
      (InteriorProgress.hab_column w.frame.fullDim w.column)
      (InteriorProgress.hOne_column w.frame.fullDim w.column) := rfl

/-- The merged vertex of `W4WallExhaustion` *is* Part I's wall vertex. -/
theorem mergeVertex_eq (w : Regrowth core y degree) :
    W4WallExhaustion.mergeVertex w = ⟨InteriorProgress.leftEnd w.frame.fullDim w.column,
      InteriorProgress.hab_column w.frame.fullDim w.column⟩ := rfl

/-! ## 3.  The classification of the limit, and what the valency pins -/

/-- **The ten-way classification of a regrowth's limit.**  Part I's interior
classifier at the regrowth's own cover and column, with all three wall-degeneration
receipts discharged from `admissibleColumn`.  Its constructors carry exactly the inputs
the balancing identities take: `.w4 star input` (`AuxR0SourceInput`), `.w3 star input
profile` (`W3SourceInput` + Figures 28--31 profile), `.w2 star input profile`
(`W2SourceInput` + Equations (6)--(10) profile), all over `w.limit`. -/
theorem nonempty_classification (w : Regrowth core y degree) (hy : Nondegenerate y) :
    Nonempty (IncomingSourceCases.Classification w.limit (W4WallExhaustion.mergeVertex w)) :=
  InteriorProgress.nonempty_classification_of_admissibleColumn w.frame.fullDim w.column
    (admissibleColumn w hy)

/-- A chosen classification of the regrowth's limit. -/
noncomputable def classification (w : Regrowth core y degree) (hy : Nondegenerate y) :
    IncomingSourceCases.Classification w.limit (W4WallExhaustion.mergeVertex w) :=
  (nonempty_classification w hy).some

/-- **The source case of a regrowth** (of the chosen classification). -/
noncomputable def sourceCase (w : Regrowth core y degree) (hy : Nondegenerate y) :
    SourceCase :=
  (classification w hy).sourceCase

/-- The wall valency each of the ten tags lives at. -/
def tagValency : SourceCase → ℕ
  | .w4 => 4
  | .w3Four => 3
  | .w3Shift => 3
  | .w3Nd3CoarseFine => 3
  | .w3Nd2CoarseFine => 3
  | .w2M11 => 2
  | .w2M1k => 2
  | .w2Mkk => 2
  | .w2P => 2
  | .w2R1 => 2

/-- **The valency pins the valency class of the tag**, for every classification: a
classification's star is a labelling `Fin k ≃` incident occurrences, and `k` is read off
its tag. -/
theorem card_incidentEdges_eq_tagValency {target : CFGraph.{0}}
    {data : GluingDatum target degree} {wall : target.V}
    (cls : IncomingSourceCases.Classification data wall) :
    (GluingDatum.incidentEdges wall).card = tagValency cls.sourceCase := by
  cases cls with
  | w4 star _ => exact star.card_incidentEdges
  | w3 star _ profile => cases profile <;> exact star.card_incidentEdges
  | w2 star _ profile => cases profile <;> exact star.card_incidentEdges

/-- A classification has tag `w4` exactly at a four-valent wall. -/
theorem sourceCase_eq_w4_iff {target : CFGraph.{0}} {data : GluingDatum target degree}
    {wall : target.V} (cls : IncomingSourceCases.Classification data wall) :
    cls.sourceCase = .w4 ↔ (GluingDatum.incidentEdges wall).card = 4 := by
  rw [card_incidentEdges_eq_tagValency cls]
  generalize cls.sourceCase = tag
  cases tag <;> decide

/-- **At a four-valent wall the tag is `w4`**, whichever classification is chosen. -/
theorem sourceCase_eq_w4 (w : Regrowth core y degree) (hy : Nondegenerate y)
    (hFour : (GluingDatum.incidentEdges (W4WallExhaustion.mergeVertex w)).card = 4) :
    sourceCase w hy = .w4 :=
  (sourceCase_eq_w4_iff (classification w hy)).mpr hFour

/-- Every regrowth's wall is divalent, trivalent or four-valent. -/
theorem card_incidentEdges_mem (w : Regrowth core y degree) (hy : Nondegenerate y) :
    (GluingDatum.incidentEdges (W4WallExhaustion.mergeVertex w)).card = 2 ∨
      (GluingDatum.incidentEdges (W4WallExhaustion.mergeVertex w)).card = 3 ∨
      (GluingDatum.incidentEdges (W4WallExhaustion.mergeVertex w)).card = 4 := by
  rw [card_incidentEdges_eq_tagValency (classification w hy)]
  generalize (classification w hy).sourceCase = tag
  cases tag <;> decide

/-! ## 4.  The routed wall, at every tag -/

/-- The regrowth's own constructed dart graph. -/
noncomputable abbrev ownGraph (w : Regrowth core y degree) :=
  StableSourceDarts.ofDatum w.frame.data w.frame.fullDim.connected w.frame.fullDim.trivalent
    w.frame.fullDim.pathEnds

/-- Its literal row labels. -/
noncomputable abbrev ownLabel (w : Regrowth core y degree) :=
  fun d ↦ w.frame.fullDim.labelling.row (StableSourceDarts.row w.frame.data d)

/-- **The tracked routed wall of a regrowth**, at every tag: Part I's A04 at the
regrowth's own chart, cover, column and self-tracking. -/
theorem nonempty_trackedRoutedWall (w : Regrowth core y degree) (hy : Nondegenerate y) :
    Nonempty (TrackedWallProgress.TrackedRoutedWall degree (Fin p) w.frame.matrix w.column
      (ownGraph w) (ownLabel w)) :=
  InteriorBridgesAll.wallBridge _ w.frame.data w.frame.fullDim w.column rfl
    (InteriorGraphTracking.Tracks.self w.frame.fullDim) (admissibleColumn w hy)

/-- The untracked routed wall. -/
theorem nonempty_routedWall (w : Regrowth core y degree) (hy : Nondegenerate y) :
    Nonempty (A04MoreTags.RoutedWall degree (Fin p) w.frame.matrix w.column) :=
  (nonempty_trackedRoutedWall w hy).elim fun r ↦ ⟨r.toRoutedWall⟩

/-- **A wall input at the regrowth's column**, with a nonsingular member presenting the
regrowth's own length matrix and regrown column equal to the regrowth's column. -/
theorem exists_wallInput (w : Regrowth core y degree) (hy : Nondegenerate y) :
    ∃ input : WallProgress.WallInput degree (Fin p) w.column,
      ∃ incoming : Fin input.case.arity,
        (GluingDatum.LengthMatrixPresentation.matrix
          (input.family.presentation incoming)).det ≠ 0 ∧
        GluingDatum.LengthMatrixPresentation.matrix (input.family.presentation incoming) =
          w.frame.matrix ∧
        input.family.wallColumn = w.column := by
  obtain ⟨r⟩ := nonempty_routedWall w hy
  exact ⟨r.input, r.incoming, r.incomingNonzero, r.incomingMatrix, r.input.family_wallColumn⟩

/-! ## 5.  The faithful four-valent route -/

section W4

/-- **Equation (1)'s source input at a regrowth's four-valent wall.**  Every field is
read off the regrowth and its positive request (`InheritedLimitRows`,
`InheritedLimitBranches`); the `FourStar` witnesses the valency. -/
theorem w4Input (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)) :
    W4StableSource.AuxR0SourceInput w.limit star :=
  W4PositiveExit.wallInput w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) star
    (InheritedLimitRows.forest w hy) (InheritedLimitRows.danglingCompatible w hy)
    ⟨InheritedLimitRows.rowEquiv w hy⟩
    (fun _ ↦ InheritedLimitBranches.limit_trivalent w hy _)

/-- The `w4` classification, with no choice. -/
noncomputable def w4Classification (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)) :
    IncomingSourceCases.Classification w.limit (W4WallExhaustion.mergeVertex w) :=
  .w4 star (w4Input w hy star)

theorem w4Classification_sourceCase (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)) :
    (w4Classification w hy star).sourceCase = .w4 := rfl

/-- **The regrowth's own index in Equation (1)'s family**: Part I's pairing of the
regrowth's own cover, read against `star`. -/
noncomputable def w4Incoming (w : Regrowth core y degree)
    (star : FourStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)) :
    Fin 3 :=
  W4IncomingTargetNormalization.pairing w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) star

/-- **The regrowth's own cover is a full-dimensional member of the family**, at its
own pairing, with its own matrix, its own column and its own tracking
(`InteriorGraphTracking.exists_matched_tracking`). -/
theorem exists_w4Matched (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)) :
    ∃ matched : FullDimensionalSource.FullDimensionalSourcePresentation
        (W4OutgoingStableRows.member (w4Input w hy star) (w4Incoming w star)).datum (Fin p),
      Nonempty (InteriorGraphTracking.Tracks matched (ownGraph w) (ownLabel w)) ∧
      GluingDatum.LengthMatrixPresentation.matrix matched.labelling.presentation =
        w.frame.matrix ∧
      W4PositiveExit.wallColumn (w4Input w hy star) (w4Incoming w star) matched =
        w.column := by
  obtain ⟨matched, hTrack, hMatrix, -, hColumn⟩ :=
    InteriorGraphTracking.exists_matched_tracking w.frame.data w.frame.fullDim
      (InteriorGraphTracking.Tracks.self w.frame.fullDim) rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) star
      (InheritedLimitRows.forest w hy) (InheritedLimitRows.danglingCompatible w hy)
      (w4Input w hy star)
  refine ⟨matched, hTrack, hMatrix, ?_⟩
  exact (W4PositiveExit.wallColumn_eq _ _ matched).trans
    (hColumn.trans (InteriorProgress.targetEdge_symm_contractedEdge w.frame.fullDim w.column))

/-- The matched presentation. -/
noncomputable def w4Matched (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)) :
    FullDimensionalSource.FullDimensionalSourcePresentation
      (W4OutgoingStableRows.member (w4Input w hy star) (w4Incoming w star)).datum (Fin p) :=
  Classical.choose (exists_w4Matched w hy star)

/-- **The faithful `w4` tracked routed wall of a regrowth.**  `w4Bridge_w4`'s recipe,
built rather than hidden behind `Nonempty`: the wall input is
`A04FourTags.ofFourValentHonest` over `w.limit` at the merged vertex, and the incoming
member is `w4Incoming`. -/
noncomputable def w4Routed (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)) :
    TrackedWallProgress.TrackedRoutedWall degree (Fin p) w.frame.matrix w.column
      (ownGraph w) (ownLabel w) :=
  TrackedWallProgress.trackedW4 (wall := w.column) (w4Input w hy star)
    (graph_connected_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) w.frame.fullDim.targetConnected)
    ((genus_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column)).trans w.frame.fullDim.targetGenus)
    (w4Incoming w star) (w4Matched w hy star)
    (Classical.choose_spec (exists_w4Matched w hy star)).2.2
    (W4WallExhaustion.mergeVertex w) w.frame.matrix (w4Incoming w star)
    (W4PositiveExit.incomingDet_ne_zero _ _ (w4Matched w hy star))
    ((W4PositiveExit.memberMatrix_self _ _ (w4Matched w hy star)).trans
      (Classical.choose_spec (exists_w4Matched w hy star)).2.1)
    (Classical.choose_spec (exists_w4Matched w hy star)).1.some

/-- **The regrowth's `w4` wall input.** -/
noncomputable def w4WallInput (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)) :
    WallProgress.WallInput degree (Fin p) w.column :=
  (w4Routed w hy star).toRoutedWall.input

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w))

theorem w4Routed_case : (w4Routed w hy star).toRoutedWall.input.case = .w4 := rfl

theorem w4Routed_target :
    (w4Routed w hy star).toRoutedWall.input.target = w.frame.limitTarget w.column := rfl

theorem w4Routed_data : (w4Routed w hy star).toRoutedWall.input.data = w.limit := rfl

theorem w4Routed_wallVertex :
    (w4Routed w hy star).toRoutedWall.input.wallVertex = W4WallExhaustion.mergeVertex w := rfl

theorem w4Routed_incoming :
    (w4Routed w hy star).toRoutedWall.incoming = w4Incoming w star := rfl

end W4

/-! ## 6.  The balancing identities, read at the regrowth's limit -/

section Balances

/-- **Equation (1) at every four-valent regrowth, with no receipt.**
`W4FullDimensionalBalance.sum_signedMult_eq_zero` needs one datum beyond the family --
a full-dimensional presentation of an incoming member -- and the regrowth's own cover,
matched by Part I at its own pairing (`w4Matched`), is one. -/
theorem w4_sum_signedMult_eq_zero (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w))
    (initial : W4StableSource.StableLengthMatrixLabelling
      (W4OutgoingStableRows.member (w4Input w hy star) 0).datum (Fin p)) :
    ∑ pairing : Fin 3, signedMult
      (W4CommonBalance.labelling (w4Input w hy star) initial pairing).presentation = 0 :=
  W4FullDimensionalBalance.sum_signedMult_eq_zero (w4Input w hy star) (w4Incoming w star)
    initial (w4Matched w hy star)

/-- The canonical coordinate order of the W3 balances is stated with a classical
decision procedure on `Option target.edges`; this local instance makes the statements
below elaborate against it. -/
noncomputable local instance instDecidableEqOptionEdges {target : CFGraph} :
    DecidableEq (Option target.edges) := Classical.decEq _

/-- **Equation (4) at every regrowth tagged `w3Nd3CoarseFine`**, from the
classification's own payload and nothing else. -/
theorem exists_w3Nd3_balance (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (W4WallExhaustion.mergeVertex w))
    (htag : cls.sourceCase = .w3Nd3CoarseFine) :
    ∃ (star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column)
        (W4WallExhaustion.mergeVertex w))
      (input : ThirdEquation.W3SourceInput w.limit star)
      (profile : W3R1SourceProfile.Nd3Profile w.limit
        (ThirdEquation.W3SourceInput.distinguishedBlock input))
      (hSame : profile.first.1.1.1 = profile.second.1.1.1),
      ∑ position : Fin 2, signedMult (W3Nd3CommonBalance.labelling input profile hSame
        (W3Nd3CommonBalance.canonicalInitialLabelling input profile hSame)
          position).presentation = 0 := by
  cases cls with
  | w4 => cases htag
  | w3 star input profile =>
    cases profile with
    | nd3CoarseFine profile hSame _ _ =>
      exact ⟨star, input, profile, hSame,
        W3Nd3UnitBalance.sum_signedMult_canonical_eq_zero input profile hSame⟩
    | four => cases htag
    | shift => cases htag
    | nd2CoarseFine => cases htag
  | w2 _ _ profile => cases profile <;> cases htag

/-- **Equation (5) at every regrowth tagged `w3Nd2CoarseFine`**, from the
classification's own payload and nothing else. -/
theorem exists_w3Nd2_balance (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (W4WallExhaustion.mergeVertex w))
    (htag : cls.sourceCase = .w3Nd2CoarseFine) :
    ∃ (star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column)
        (W4WallExhaustion.mergeVertex w))
      (input : ThirdEquation.W3SourceInput w.limit star)
      (profile : W3R1SourceProfile.Nd2Profile w.limit
        (ThirdEquation.W3SourceInput.distinguishedBlock input)),
      ∑ position : Fin 2, signedMult (W3Nd2CommonBalance.labelling input profile
        (W3Nd2CommonBalance.canonicalInitialLabelling input profile)
          position).presentation = 0 := by
  cases cls with
  | w4 => cases htag
  | w3 star input profile =>
    cases profile with
    | nd2CoarseFine profile =>
      exact ⟨star, input, profile,
        W3Nd2UnitBalance.sum_signedMult_canonical_eq_zero input profile⟩
    | four => cases htag
    | shift => cases htag
    | nd3CoarseFine => cases htag
  | w2 _ _ profile => cases profile <;> cases htag

/-- **Equation (10) at every regrowth tagged `w2R1`**: the `r1` profile is a `Pair`
(`W2R1ArbitraryIncomingExit.exists_w2R1_payload`), and the balance takes nothing else. -/
theorem exists_w2R1_balance (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (W4WallExhaustion.mergeVertex w))
    (htag : cls.sourceCase = .w2R1) :
    ∃ (star : W2R1Target.TwoStar (w.frame.limitTarget w.column)
        (W4WallExhaustion.mergeVertex w))
      (input : SecondEquation.W2SourceInput w.limit star)
      (pair : W2R1SourceCandidates.Pair w.limit star),
      ∑ position : Fin 2, signedMult ((W2R1LimitMatrix.limitColumns pair input.valid).labelling
        ((W2R1LimitMatrix.limitColumns pair input.valid).canonicalInitialLabelling input)
          position).presentation = 0 := by
  cases cls with
  | w4 => cases htag
  | w3 _ _ profile => cases profile <;> cases htag
  | w2 star input profile =>
    obtain ⟨pair⟩ := W2R1ArbitraryIncomingExit.exists_w2R1_payload w.frame.data
      (InteriorProgress.hc_column w.frame.fullDim w.column)
      (InteriorProgress.hab_column w.frame.fullDim w.column)
      (InteriorProgress.hOne_column w.frame.fullDim w.column) star input profile htag
    exact ⟨star, input, pair, W2R1UnitBalance.sum_signedMult_canonical_eq_zero pair input⟩

/-- **Equation (9) at every regrowth tagged `w2P`**: the `p` profile's payload, and the
incoming full-dimensional member the balance needs is the regrowth's own cover, matched
by Part I (`W2PGraphTracking.exists_matched_tracking`). -/
theorem exists_w2P_balance (w : Regrowth core y degree) (hy : Nondegenerate y)
    (cls : IncomingSourceCases.Classification w.limit (W4WallExhaustion.mergeVertex w))
    (htag : cls.sourceCase = .w2P) :
    ∃ (star : W2R1Target.TwoStar (w.frame.limitTarget w.column)
        (W4WallExhaustion.mergeVertex w))
      (input : SecondEquation.W2SourceInput w.limit star)
      (wallBlock : W4Assembly.WallBlock w.limit (W4WallExhaustion.mergeVertex w))
      (profile : W2R2SourceProfile.SourceProfile w.limit star wallBlock)
      (shape : W2PSourceCandidates.Shape profile) (incoming : Fin 3)
      (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
        (W2PCommonBalance.members profile shape incoming).datum (Fin p)),
      ∑ position : Fin 3, signedMult (W2PArbitraryExit.outgoingLabelling input shape incoming
        incomingFD position).presentation = 0 := by
  cases cls with
  | w4 => cases htag
  | w3 _ _ profile => cases profile <;> cases htag
  | w2 star input profile =>
    obtain ⟨wallBlock, sourceProfile, shape, hBackground⟩ :=
      W2PArbitraryIncomingExit.exists_w2P_payload w.frame.data
        (InteriorProgress.hc_column w.frame.fullDim w.column)
        (InteriorProgress.hab_column w.frame.fullDim w.column)
        (InteriorProgress.hOne_column w.frame.fullDim w.column) star input profile htag
    obtain ⟨position, fd, -, -, -, -, -⟩ :=
      W2PGraphTracking.exists_matched_tracking w.frame.data
        (InteriorProgress.hc_column w.frame.fullDim w.column)
        (InteriorProgress.hab_column w.frame.fullDim w.column)
        (InteriorProgress.hOne_column w.frame.fullDim w.column) w.frame.fullDim
        (InheritedLimitRows.forest w hy) star sourceProfile shape hBackground
        (InteriorGraphTracking.Tracks.self w.frame.fullDim)
    exact ⟨star, input, wallBlock, sourceProfile, shape, position, fd,
      W2PMultiplicityBalance.sum_signedMult_eq_zero input shape
        (graph_connected_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
          (w.frame.numEdges_edgeOf w.column) w.frame.fullDim.targetConnected)
        ((genus_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
          (w.frame.numEdges_edgeOf w.column)).trans w.frame.fullDim.targetGenus)
        position fd⟩

end Balances

/-! ## 7.  The per-family split of `hstar` -/

/-- **The `hstar` clause at one regrowth**: its labelled geometric star carries an even
number of odd classes.  *Interface*: definitionally the summand of
`WallSwitchingBridge.countLink_of_even_stars`'s `hstar`. -/
def StarParityAt (hy : Nondegenerate y) (w : Regrowth core y degree) : Prop :=
  Even (Nat.card {c : GeometricFibre core y degree //
    GeometricStar.IsStarClass hy w c ∧ c.IsOdd})

/-- **The per-family obligation.**  At every core, every positive request
and every regrowth whose limit admits a classification with tag `tag`, the star parity
holds.  *Interface*: `(∀ tag, FamilyStarParity degree n p tag)` is equivalent to the
`hstars` antecedent of `SimpleWallSupply.inConeSupplySimple_of_even_stars`
(`familyStarParity_iff`); `StarSupplyAssembly` proves it one `tag` at a time. -/
def FamilyStarParity (degree n p : ℕ) (tag : SourceCase) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (W4WallExhaustion.mergeVertex w)),
    cls.sourceCase = tag → StarParityAt hy w

/-- The ten families together give the clause at every regrowth: every regrowth's
limit is classified (§3). -/
theorem starParityAt_of_family (h : ∀ tag, FamilyStarParity degree n p tag)
    (hy : Nondegenerate y) (w : Regrowth core y degree) : StarParityAt hy w :=
  h (classification w hy).sourceCase core y hy w (classification w hy) rfl

/-- **The per-family split is equivalent to the clause at every regrowth.** -/
theorem familyStarParity_iff :
    (∀ tag, FamilyStarParity degree n p tag) ↔
      ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y)
        (w : Regrowth core y degree), StarParityAt hy w :=
  ⟨fun h _ _ hy w ↦ starParityAt_of_family h hy w,
    fun h _ core y hy w _ _ ↦ h core y hy w⟩

/-- **The ten per-family parities give the trivalent-wall supply**
`SimpleWallSupply.InConeSupplySimple` (step 2 of `DraismaVargasCount.Assembly`). -/
theorem inConeSupplySimple_of_familyStarParity
    (h : ∀ tag, FamilyStarParity degree n p tag) :
    SimpleWallSupply.InConeSupplySimple degree n p :=
  SimpleWallSupply.inConeSupplySimple_of_even_stars
    fun _ _ _ hy w ↦ starParityAt_of_family h hy w

end DraismaVargas.Count.RegrowthWallInput
