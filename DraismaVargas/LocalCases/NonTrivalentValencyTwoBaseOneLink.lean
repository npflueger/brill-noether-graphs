import DraismaVargas.LocalCases.NonTrivalentValencyTwoDispatcher
import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneStarCount
import DraismaVargas.LocalCases.NonTrivalentValencyThreeDispatcher
import DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitStarCount

/-!
# Plugging Base I and the split member into the valency-two dispatcher: the walk's `link`

Source: Vargas, Part II, Section 5.1 (the labelling convention at a
non-trivalent wall) and Section 5.4, case `{v2-nd4}` (Configuration A puts two
survivors over each target direction; the Base I member needs the two index
equalities stated at the opening of Section 5.4 and does not exist when they
fail -- subcase `{v2-nd4-t3-k2<k3}`, and Configuration B; the Configuration A
**split** members need the strict index inequalities of the subcases
`{v2-nd4-t3-k2=k3}` and `{v2-nd4-t3-k2<k3}`; and the closing count of the
valency-two analysis, exactly one full-dimensional morphism of each type, means
that exactly one of the two families realises each cross pairing), together
with Draisma--Vargas Part I (the stable graph and its row labels, and Case
`{w2-r2}`, Base I).

`NonTrivalentValencyTwoDispatcher` reduces every valency-two move to a single
cross-pair hypothesis `CrossPairLink`, split along the dilation-index dichotomy into
`BaseOneCrossLink` (equal indices) and `SplitCrossLink` (unequal).
`NonTrivalentValencyTwoBaseOneStarCount` and `NonTrivalentValencyTwoSplitStarCount`
reduce the two families to the row-level conditions (H-BaseI)
`PrescribedBaseOneMove` and (H-split) `PrescribedSplitMove`.
**This module discharges both**, hence `CrossPairLink`, hence the valency-two branch of
the walk's `link` binder, hence -- with `NonTrivalentValencyFourDispatcher` at valency
four and `NonTrivalentValencyThreeDispatcher` at valency three -- the whole binder,
with no hypothesis left.

## What is proved

### 1.  The Base I identification over the alignment gauge

`exists_gauged_candidate_of_contraction'` is
`NonTrivalentValencyTwoGauge.exists_gauged_candidate_of_contraction` with the two pair
conjuncts its proof obtains from `exists_baseOne_candidate_of_prescribed` and then
discards, returned in the gauged datum: the prescribed cross pair
`(thickFirst, thinFirst)` meets above `t_2`, and so does the complementary pair
`(thickSecond, thinSecond)`.

`crossPair_identification` carries the mathematical content.  `BaseOneSetup` is a
`Prop`, so `setup.firstOf 0` -- and hence the cross pair `crossThick setup false`,
`crossThin setup false` that (H-BaseI) names at `A_1` -- is a classical choice, and
nothing in the conclusion of `NonTrivalentValencyTwoGauge` says which of the two
prescribed pairs it is.  It is
one of them: the gauged direction fibre over `t_2` is
`{survivorEquiv thickFirst, survivorEquiv thickSecond}`, so the thick member of the
`A_1` pair is one of the two; and the thin member is then forced, because the two
`t_2`-classes inside the anchor are distinct (`not_rel_occurrenceSheet`) while each of
the two thin survivors meets exactly one of them (the two returned pair conjuncts).

### 2.  (H-BaseI) and (H-split) from the row condition, without an order

`prescribedBaseOneMove_of_unordered_rows`: the survivor clause of
`PrescribedBaseOneMove` is an unordered statement about the moved star (a `Finset`
pair), so the two darts `thirdBase m`, `m.right` that `movedStar_base` names can be
handed to it in either order.  This is what makes the dispatcher's two row orders
`(rowT, rowR)` and `(rowR, rowT)` both admissible.  The same argument is inlined for
(H-split) in `link_of_splitAnchor`.

`crossLift_stablePath_eq_survRow` / `splitLift_stablePath_eq_survRow`: once a member of
the pair is identified with a named surviving occurrence of the wall datum, the row
(H-BaseI) / (H-split) asks for is that occurrence's incoming row `survRow`.

### 3.  The rows of the complementary pair

`rows_of_complement` (with the elementary counting lemma `pair_of_counts`): the
census `NonTrivalentValencyTwoDispatcher.card_filter_anchor_eq` says the four
survivors at the anchor carry the four
rows the move sorts at the two ends of the vanishing row, occurrence for occurrence.
So if two of them carry `rowT` and `rowR` -- the pair the move names -- the other two
carry `rowL` and `rowS`, in one of the two orders; no distinctness of the four rows is
assumed.

### 4.  The Base I half

`link_of_gauged_setup` (the link from a gauged setup whose `A_1` pair carries the two
rows the move names), `link_of_crossPair_oriented` (the two prescribed pairs built from
the named cross pair and the second index equality via
`TwoBranchAnchor.direction_index_sum`, then the dispatch on
`crossPair_identification`: if the `A_1` pair is the move's own pair the link is for
`m`; if it is the complementary pair, whose rows are `rowL`, `rowS` by item 3, the same
construction is run for `m.swap`, whose own pair is exactly the complementary one
(`movedStar_op`), and transported back by
`NonTrivalentValencyFourDispatcher.linkOfSwap`), `link_of_crossPair` (the direction of
each member read off by `survivorLabel`) and `baseOneCrossLink`:

> `∀ m wd h2, NonTrivalentValencyTwoDispatcher.BaseOneCrossLink m wd h2`.

### 5.  The split half

`link_of_splitAnchor`, `link_of_splitPair_oriented`, `link_of_splitPair_dir`,
`link_of_splitPair`, `splitCrossLink`:
`∀ m wd h2, NonTrivalentValencyTwoDispatcher.SplitCrossLink m wd h2`.  Here
`NonTrivalentValencyTwoSplitRows.SplitAnchor` is *data*, built by
`NonTrivalentValencyTwoSplitRows.splitAnchor_gauged` with its `alphaEdge`, `deltaEdge`
fields literally the images of the two named survivors, so no identification lemma is
needed and neither is `m.swap`; what is needed instead is the mirror member at
`NonTrivalentValencyTwoSplitExit.relabelStar`, for the orientation in which the larger
dilation index sits over the second direction.

### 6.  The dispatch

`crossPairLink` ((H-cross) discharged, by the index dichotomy), `link_two`
(`Nonempty (OuterWalk.TypeChangeLink m wd)` at **every** two-valent wall with no
hypothesis), `typeChangeLink_two'`, and `link_all`: the `link` binder of
`OuterWalk.coneEntry_of_reaches` with **no hypothesis at all**.
`crossPairLink_of_splitCrossLink`, `typeChangeLink_two_of_splitCrossLink` and
`link_of_splitCrossLink` are the weaker forms that take the split half as an input;
they are kept because they are what a reader checking the Base I half alone should
use.

`RetainedClassInjectivity.nonempty_evenSubdivisionPencil` feeds `link_all` to the
outer walk.

## Hypotheses

1. None at the link: `baseOneCrossLink`, `splitCrossLink`, `crossPairLink`,
   `link_two` and `link_all` carry no receipt, no no-return hypothesis, no
   Configuration receipt and no choice of outgoing type.  The Configuration A `2 + 2`
   split and the `TwoBranchAnchor` classifier are produced inside
   `NonTrivalentValencyTwoDispatcher.link_or_crossPair` from the wall metric.
2. No structure and no `Prop` is introduced by this module.  The three `Prop`s
   `BaseOneCrossLink`, `SplitCrossLink`, `CrossPairLink` of
   `NonTrivalentValencyTwoDispatcher` are non-vacuous in the absolute sense:
   `baseOneCrossLink`, `splitCrossLink` and `crossPairLink` inhabit them at every
   two-valent wall datum.

## Used by

The `link` binder of `OuterWalk.coneEntry_of_reaches`, and through it the
even-genus pencil theorems `StatementFromLink.nonempty_evenSubdivisionPencil_of_link`
and `RetainedClassInjectivity.nonempty_evenSubdivisionPencil`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneLink

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.ContractionFibre
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneTracks
open DraismaVargas.LocalCases.NonTrivalentValencyTwoDispatcher
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv (OrdinaryTrivalent)
open DraismaVargas.LocalCases.NonTrivalentValencyTwoTracksLeaf (AnchorEnds)
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

/-- Two occurrences counted once each against a two-element multiset. -/
theorem pair_of_counts {α : Type*} [DecidableEq α] {x y u v : α}
    (h1 : (if x = u then 1 else 0) + (if y = u then 1 else 0) = 1 + (if v = u then 1 else 0))
    (h2 : (if x = v then 1 else 0) + (if y = v then 1 else 0) = 1 + (if u = v then 1 else 0)) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  classical
  by_cases huv : u = v
  · rw [if_pos (show v = u from huv.symm)] at h1
    refine Or.inl ⟨?_, ?_⟩
    · by_contra hx
      rw [if_neg (show ¬ (x = u) from hx)] at h1
      by_cases hy : y = u
      · rw [if_pos (show y = u from hy)] at h1; omega
      · rw [if_neg (show ¬ (y = u) from hy)] at h1; omega
    · by_contra hy
      rw [if_neg (show ¬ (y = u) from fun h ↦ hy (h.trans huv))] at h1
      by_cases hx : x = u
      · rw [if_pos (show x = u from hx)] at h1; omega
      · rw [if_neg (show ¬ (x = u) from hx)] at h1; omega
  · rw [if_neg (show ¬ (v = u) from fun h ↦ huv h.symm)] at h1
    rw [if_neg (show ¬ (u = v) from huv)] at h2
    by_cases hx : x = u
    · have hy : ¬ y = u := by
        intro hy
        rw [if_pos (show x = u from hx), if_pos (show y = u from hy)] at h1
        omega
      have hxv : ¬ x = v := fun h ↦ huv (hx.symm.trans h)
      refine Or.inl ⟨hx, ?_⟩
      by_contra hyv
      rw [if_neg (show ¬ (x = v) from hxv), if_neg (show ¬ (y = v) from hyv)] at h2
      omega
    · have hy : y = u := by
        by_contra hy
        rw [if_neg (show ¬ (x = u) from hx), if_neg (show ¬ (y = u) from hy)] at h1
        omega
      have hyv : ¬ y = v := fun h ↦ huv (hy.symm.trans h)
      refine Or.inr ⟨?_, hy⟩
      by_contra hxv
      rw [if_neg (show ¬ (x = v) from hxv), if_neg (show ¬ (y = v) from hyv)] at h2
      omega

section Wall

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (thickSheet thinSheet : Fin deg)

variable (setup : BaseOneSetup
    (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet) wallStar
    (gaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet))

/-- The stable row of one member of the cross pair at `A₁`, read on the incoming
cover, is the incoming row of the surviving occurrence it names. -/
theorem crossLift_stablePath_eq_survRow (side dir : Bool)
    (e : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (h : (ungaugeSurvivor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      thickSheet thinSheet (crossSurvivor setup side dir)).1 = e.1) :
    (crossLift m wd thickSheet thinSheet setup side dir).stablePath = survRow m wd e := by
  have hEq : crossWallEdge m wd thickSheet thinSheet setup side dir = e := Subtype.ext h
  rw [crossLift_stablePath m wd thickSheet thinSheet setup side dir, hEq]
  rfl

/-- **(H-BaseI) from the unordered row condition at `A₁`.**  The move always
places one dart at each anchor end (`exists_movedStar_darts_at_ends`), and the
survivor clause of `PrescribedBaseOneMove` does not order the pair, so either
assignment of the two rows discharges it. -/
theorem prescribedBaseOneMove_of_unordered_rows
    (hA1 : ((crossLift m wd thickSheet thinSheet setup false false).stablePath = rowT m wd ∧
          (crossLift m wd thickSheet thinSheet setup false true).stablePath = rowR m wd) ∨
        ((crossLift m wd thickSheet thinSheet setup false false).stablePath = rowR m wd ∧
          (crossLift m wd thickSheet thinSheet setup false true).stablePath = rowT m wd)) :
    PrescribedBaseOneMove m wd thickSheet thinSheet setup (baseEnd m wd) (opEnd m wd) := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rcases hA1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨coverDart m wd (thirdBase m), coverDart m wd m.right, h1.symm, h2.symm, ?_⟩
    rw [movedStar_base m, dart_coverDart, dart_coverDart]
  · refine ⟨coverDart m wd m.right, coverDart m wd (thirdBase m), h1.symm, h2.symm, ?_⟩
    rw [movedStar_base m, dart_coverDart, dart_coverDart,
      Finset.pair_comm (thirdBase m) m.right]

/-- **The rows of the complementary cross pair.**  The four survivors at the
anchor carry the four rows the move sorts at the two ends of the vanishing row,
occurrence for occurrence (`card_filter_anchor_eq`); so if two of them carry the
rows of the pair the move names, the other two carry the rows of the
complementary pair. -/
theorem rows_of_complement
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩ anchorBlk)
    (hEnds : AnchorEnds m wd anchorBlk (baseEnd m wd) (opEnd m wd))
    (A B C E : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hA : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) A.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hB : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) B.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hC : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) C.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hE : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) E.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hAB : A ≠ B) (hAC : A ≠ C) (hAE : A ≠ E) (hBC : B ≠ C) (hBE : B ≠ E) (hCE : C ≠ E)
    (hrows : (survRow m wd A = rowT m wd ∧ survRow m wd B = rowR m wd) ∨
      (survRow m wd A = rowR m wd ∧ survRow m wd B = rowT m wd)) :
    (survRow m wd C = rowL m wd ∧ survRow m wd E = rowS m wd) ∨
      (survRow m wd C = rowS m wd ∧ survRow m wd E = rowL m wd) := by
  classical
  have hcard : ({A, B, C, E} :
      Finset (NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hAB, hAC, hAE]),
      Finset.card_insert_of_notMem (by simp [hBC, hBE]),
      Finset.card_insert_of_notMem (by simp [hCE]), Finset.card_singleton]
  have hS : incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) = {A, B, C, E} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact (mem_incidentEdges _ _ _).mpr hA
      · exact (mem_incidentEdges _ _ _).mpr hB
      · exact (mem_incidentEdges _ _ _).mpr hC
      · exact (mem_incidentEdges _ _ _).mpr hE
    · rw [card_incidentEdges,
        NonTrivalentValencyTwoTracks.nonDanglingValency_anchorVertex m wd src, hcard]
  have hsum : ∀ r : StablePath wd.cover,
      (if survRow m wd A = r then 1 else 0) + ((if survRow m wd B = r then 1 else 0) +
          ((if survRow m wd C = r then 1 else 0) + (if survRow m wd E = r then 1 else 0))) =
        ((if rowL m wd = r then 1 else 0) + (if rowT m wd = r then 1 else 0)) +
          ((if rowR m wd = r then 1 else 0) + (if rowS m wd = r then 1 else 0)) := by
    intro r
    rw [← card_filter_anchor_eq m wd hEnds src hOrd r, hS, Finset.card_filter,
      Finset.sum_insert (by simp [hAB, hAC, hAE]),
      Finset.sum_insert (by simp [hBC, hBE]),
      Finset.sum_insert (by simp [hCE]), Finset.sum_singleton]
  have hABcount : ∀ r : StablePath wd.cover,
      (if survRow m wd A = r then 1 else 0) + (if survRow m wd B = r then 1 else 0) =
        (if rowT m wd = r then 1 else 0) + (if rowR m wd = r then 1 else 0) := by
    intro r
    rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb]
      exact Nat.add_comm _ _
  have hself : ∀ r : StablePath wd.cover, (if r = r then (1 : ℕ) else 0) = 1 :=
    fun r ↦ if_pos rfl
  have h1 : (if survRow m wd C = rowL m wd then 1 else 0) +
      (if survRow m wd E = rowL m wd then 1 else 0) =
      1 + (if rowS m wd = rowL m wd then 1 else 0) := by
    have e1 := hsum (rowL m wd)
    have e2 := hABcount (rowL m wd)
    rw [hself (rowL m wd)] at e1
    omega
  have h2 : (if survRow m wd C = rowS m wd then 1 else 0) +
      (if survRow m wd E = rowS m wd then 1 else 0) =
      1 + (if rowL m wd = rowS m wd then 1 else 0) := by
    have e1 := hsum (rowS m wd)
    have e2 := hABcount (rowS m wd)
    rw [hself (rowS m wd)] at e1
    omega
  exact pair_of_counts h1 h2

end Wall



section Producer

variable {target : CFGraph} {degree : ℕ}
variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The producer of `NonTrivalentValencyTwoGauge` with the two discarded pair
conjuncts returned, in the gauged datum where the identification needs them. -/
theorem exists_gauged_candidate_of_contraction'
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hEdge : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hEdge)
    (star : W2R1Target.TwoStar (contract target hab hEdge) ⟨a, hab⟩)
    (anchorBlock : WallBlock (contractDatum data hc hab hEdge) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hEdge)
      (WallBlock.sourceVertex (contractDatum data hc hab hEdge) ⟨a, hab⟩ anchorBlock) = 4)
    (hSplit : ∀ label : Fin 2,
      (directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock label).card = 2)
    (thickFirst thickSecond thinFirst thinSecond :
      IncidentSourceEdge (contractDatum data hc hab hEdge)
        (WallBlock.sourceVertex (contractDatum data hc hab hEdge) ⟨a, hab⟩ anchorBlock))
    (hThickFirst : thickFirst ∈
      directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock 0)
    (hThickSecond : thickSecond ∈
      directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock 0)
    (hThinFirst : thinFirst ∈
      directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock 1)
    (hThinSecond : thinSecond ∈
      directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock 1)
    (hThickNe : thickFirst ≠ thickSecond) (hThinNe : thinFirst ≠ thinSecond)
    (hIndexFirst : (contractDatum data hc hab hEdge).sourceEdgeIndex thickFirst.1 =
      (contractDatum data hc hab hEdge).sourceEdgeIndex thinFirst.1)
    (hIndexSecond : (contractDatum data hc hab hEdge).sourceEdgeIndex thickSecond.1 =
      (contractDatum data hc hab hEdge).sourceEdgeIndex thinSecond.1) :
    ∃ setup : BaseOneSetup
        (gaugedData (contractDatum data hc hab hEdge) star anchorBlock
          (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)) star
        (gaugedAnchor (contractDatum data hc hab hEdge) star anchorBlock
          (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)),
      ∃ outgoing : BalancedGlobal.Candidate (contract target hab hEdge) degree
          (gaugedData (contractDatum data hc hab hEdge) star anchorBlock
            (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)) ⟨a, hab⟩,
        outgoing.datum.Valid ∧
          outgoing.resolution anchorBlock.1 = selectedResolution setup ∧
            (gaugedData (contractDatum data hc hab hEdge) star anchorBlock
                (occurrenceSheet thickFirst)
                (occurrenceSheet thinFirst)).vertexPartition ⟨a, hab⟩ =
              (contractDatum data hc hab hEdge).vertexPartition ⟨a, hab⟩ ∧
            (outgoing.resolution anchorBlock.1).left.blockCard setup.foldFirst = 2 ∧
            (∀ sheet, ((contractDatum data hc hab hEdge).vertexPartition ⟨a, hab⟩).Rel
                anchorBlock.1 sheet →
              outgoing.datum.sourceEdgeIndex (outgoing.newSourceEdge sheet) = 1) ∧
            ((gaugedData (contractDatum data hc hab hEdge) star anchorBlock
                  (occurrenceSheet thickFirst)
                  (occurrenceSheet thinFirst)).edgePartition (star.edge 0)).Rel
              (occurrenceSheet (survivorEquiv (contractDatum data hc hab hEdge) star anchorBlock
                (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) thickFirst))
              (occurrenceSheet (survivorEquiv (contractDatum data hc hab hEdge) star anchorBlock
                (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) thinFirst)) ∧
            ((gaugedData (contractDatum data hc hab hEdge) star anchorBlock
                  (occurrenceSheet thickFirst)
                  (occurrenceSheet thinFirst)).edgePartition (star.edge 0)).Rel
              (occurrenceSheet (survivorEquiv (contractDatum data hc hab hEdge) star anchorBlock
                (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) thickSecond))
              (occurrenceSheet (survivorEquiv (contractDatum data hc hab hEdge) star anchorBlock
                (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) thinSecond)) := by
  classical
  have hConnected : graph_connected (contract target hab hEdge) :=
    graph_connected_contract target hab hEdge fd.targetConnected
  have hGenus : genus (contract target hab hEdge) = 0 :=
    (genus_contract target hab hEdge).trans fd.targetGenus
  have hValid : (contractDatum data hc hab hEdge).Valid := valid_contractDatum data hc hab hEdge hForest fd.valid
  have source : TwoBranchAnchor (contractDatum data hc hab hEdge) star anchorBlock :=
    NonTrivalentValencyTwoRigidity.twoBranchAnchor data fd hc hab hEdge hForest hCompat star
      anchorBlock hNd
  have hExists := exists_isAlignmentGauge source hSplit hThickFirst hThickSecond
    hThinFirst hThinSecond hThickNe hThinNe hIndexFirst hIndexSecond
  have hSourceConnected : (contractDatum data hc hab hEdge).Connected := hValid.1
  refine ⟨baseOneSetup_gauged (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
    (occurrenceSheet thinFirst) hConnected hGenus hSourceConnected source hSplit hExists, ?_⟩
  have hZeroSheet : ∀ edge ∈ directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock 0,
      occurrenceSheet (survivorEquiv (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) edge) = occurrenceSheet edge :=
    fun _ hE ↦ occurrenceSheet_survivorEquiv_zero (contractDatum data hc hab hEdge) star anchorBlock _ _
      hConnected hGenus hE
  have hOneSheet : ∀ edge ∈ directionSurvivors (contractDatum data hc hab hEdge) star anchorBlock 1,
      occurrenceSheet (survivorEquiv (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) edge) =
        gaugePerm (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) (occurrenceSheet edge) :=
    fun _ hE ↦ occurrenceSheet_survivorEquiv_one (contractDatum data hc hab hEdge) star anchorBlock _ _ hE
  have hMeet : ((gaugedData (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)).edgePartition (star.edge 0)).Rel
      (occurrenceSheet (survivorEquiv (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) thickFirst))
      (occurrenceSheet (survivorEquiv (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) thinFirst)) := by
    rw [gaugedData_edgePartition_zero (contractDatum data hc hab hEdge) star anchorBlock _ _ hConnected hGenus,
      hZeroSheet thickFirst hThickFirst, hOneSheet thinFirst hThinFirst]
    exact gaugePerm_pairing (contractDatum data hc hab hEdge) star anchorBlock _ _ hExists
  obtain ⟨outgoing, hOutValid, hRes, _hIndexA, _hIndexB, hPartner, _hCardFirst,
      _hCardSecond, _hNotRel, hFold, hNew⟩ :=
    exists_baseOne_candidate_of_prescribed
      (baseOneSetup_gauged (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) hConnected hGenus hSourceConnected source hSplit hExists)
      (gaugedData_valid (contractDatum data hc hab hEdge) star anchorBlock _ _ hValid)
      (mem_directionSurvivors_gauged (contractDatum data hc hab hEdge) star anchorBlock _ _ hSourceConnected 0 hThickFirst)
      (mem_directionSurvivors_gauged (contractDatum data hc hab hEdge) star anchorBlock _ _ hSourceConnected 0 hThickSecond)
      (mem_directionSurvivors_gauged (contractDatum data hc hab hEdge) star anchorBlock _ _ hSourceConnected 1 hThinFirst)
      (mem_directionSurvivors_gauged (contractDatum data hc hab hEdge) star anchorBlock _ _ hSourceConnected 1 hThinSecond)
      ((survivorEquiv (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)).injective.ne (Ne.symm hThickNe))
      ((survivorEquiv (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)).injective.ne (Ne.symm hThinNe)) hMeet
  refine ⟨outgoing, hOutValid, hRes,
    gaugedData_vertexPartition_wall (contractDatum data hc hab hEdge) star anchorBlock _ _, hFold, fun sheet hSheet ↦
      hNew sheet ?_, hMeet, hPartner⟩
  show ((gaugedData (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
    (occurrenceSheet thinFirst)).vertexPartition ⟨a, hab⟩).Rel anchorBlock.1 sheet
  rw [gaugedData_vertexPartition_wall (contractDatum data hc hab hEdge) star anchorBlock (occurrenceSheet thickFirst)
    (occurrenceSheet thinFirst)]
  exact hSheet

end Producer



section Identification

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  (base : GluingDatum target degree) (star : TwoStar target wall)
  (anchor : WallBlock base wall)

/-- **The cross pair the Base I setup puts at `A₁` is one of the two prescribed
pairs.** -/
theorem crossPair_identification
    (hConn : base.Connected)
    (hSplit : ∀ label : Fin 2, (directionSurvivors base star anchor label).card = 2)
    {thickFirst thickSecond thinFirst thinSecond :
      IncidentSourceEdge base (WallBlock.sourceVertex base wall anchor)}
    (hTF : thickFirst ∈ directionSurvivors base star anchor 0)
    (hTS : thickSecond ∈ directionSurvivors base star anchor 0)
    (hNF : thinFirst ∈ directionSurvivors base star anchor 1)
    (hNS : thinSecond ∈ directionSurvivors base star anchor 1)
    (hTNe : thickFirst ≠ thickSecond) (hNNe : thinFirst ≠ thinSecond)
    (setup : BaseOneSetup (gaugedData base star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)) star
      (gaugedAnchor base star anchor (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)))
    (hPairFirst : ((gaugedData base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst)).edgePartition (star.edge 0)).Rel
        (occurrenceSheet (survivorEquiv base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) thickFirst))
        (occurrenceSheet (survivorEquiv base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) thinFirst)))
    (hPairSecond : ((gaugedData base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst)).edgePartition (star.edge 0)).Rel
        (occurrenceSheet (survivorEquiv base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) thickSecond))
        (occurrenceSheet (survivorEquiv base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) thinSecond))) :
    (ungaugeSurvivor base star anchor (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)
          (crossThick setup false) = thickFirst ∧
        ungaugeSurvivor base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) (crossThin setup false) = thinFirst) ∨
      (ungaugeSurvivor base star anchor (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)
            (crossThick setup false) = thickSecond ∧
          ungaugeSurvivor base star anchor (occurrenceSheet thickFirst)
            (occurrenceSheet thinFirst) (crossThin setup false) = thinSecond) := by
  classical
  have hGauge0 : directionSurvivors (gaugedData base star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)) star
      (gaugedAnchor base star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)) 0 =
      {survivorEquiv base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) thickFirst,
        survivorEquiv base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) thickSecond} := by
    rw [directionSurvivors_gauged base star anchor _ _ hConn 0,
      directionSurvivors_eq_pair (hSplit 0) hTF hTS hTNe]
    simp
  have hGauge1 : directionSurvivors (gaugedData base star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)) star
      (gaugedAnchor base star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)) 1 =
      {survivorEquiv base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) thinFirst,
        survivorEquiv base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) thinSecond} := by
    rw [directionSurvivors_gauged base star anchor _ _ hConn 1,
      directionSurvivors_eq_pair (hSplit 1) hNF hNS hNNe]
    simp
  have hUn : ∀ e : IncidentSourceEdge base (WallBlock.sourceVertex base wall anchor),
      ungaugeSurvivor base star anchor (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)
        (survivorEquiv base star anchor (occurrenceSheet thickFirst)
          (occurrenceSheet thinFirst) e) = e :=
    fun e ↦ (survivorEquiv base star anchor (occurrenceSheet thickFirst)
      (occurrenceSheet thinFirst)).symm_apply_apply e
  have hThickMem := setup.firstOf_mem 0
  rw [hGauge0, Finset.mem_insert, Finset.mem_singleton] at hThickMem
  have hThinMem := crossThin_mem setup false
  rw [hGauge1, Finset.mem_insert, Finset.mem_singleton] at hThinMem
  have hMeet := crossThin_meet setup false
  rw [show anchorBranchSheet setup false =
    occurrenceSheet (crossThick setup false) from
      (occurrenceSheet_crossThick setup false).symm] at hMeet
  have hCT : crossThick setup false = setup.firstOf 0 := rfl
  have hNotRel : ¬ ((gaugedData base star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)).edgePartition (star.edge 0)).Rel
      (occurrenceSheet (survivorEquiv base star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) thickFirst))
      (occurrenceSheet (survivorEquiv base star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst) thickSecond)) :=
    not_rel_occurrenceSheet
      (mem_directionSurvivors_gauged base star anchor _ _ hConn 0 hTF)
      (mem_directionSurvivors_gauged base star anchor _ _ hConn 0 hTS)
      ((survivorEquiv base star anchor (occurrenceSheet thickFirst)
        (occurrenceSheet thinFirst)).injective.ne hTNe)
  rcases hThickMem with hT | hT
  · rw [hCT, hT] at hMeet
    rcases hThinMem with hN | hN
    · exact Or.inl ⟨by rw [hCT, hT, hUn], by rw [hN, hUn]⟩
    · rw [hN] at hMeet
      exact absurd (hPairSecond.trans hMeet).symm hNotRel
  · rw [hCT, hT] at hMeet
    rcases hThinMem with hN | hN
    · rw [hN] at hMeet
      exact absurd (hPairFirst.trans hMeet) hNotRel
    · exact Or.inr ⟨by rw [hCT, hT, hUn], by rw [hN, hUn]⟩

end Identification

/-! ## The link at a Configuration A cross pair -/

section Headline

open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneStarCount
  (typeChangeLink_of_prescribedBaseOneMove)

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {deg : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- The other member of a two-element finset. -/
theorem other_of_pair {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.card = 2)
    {a : α} (ha : a ∈ s) : ∃ b ∈ s, b ≠ a := by
  classical
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact ⟨y, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Ne.symm hxy⟩
  · rw [Finset.mem_singleton] at ha
    subst ha
    exact ⟨x, Finset.mem_insert_self _ _, hxy⟩

/-- **The link from a gauged Base I setup whose `A₁` pair carries the two rows the
move names.**  The star count of `NonTrivalentValencyTwoBaseOneStarCount` with
(H-BaseI) discharged by
`prescribedBaseOneMove_of_unordered_rows`; the wall labelling, the anchor ends and
the ordinary-block trivalence are produced from the wall data. -/
theorem link_of_gauged_setup (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (thickSheet thinSheet : Fin deg)
    (setup : BaseOneSetup
      (gaugedData (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet) wallStar
      (gaugedAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        thickSheet thinSheet))
    (hA1 : ((crossLift m wd thickSheet thinSheet setup false false).stablePath = rowT m wd ∧
          (crossLift m wd thickSheet thinSheet setup false true).stablePath = rowR m wd) ∨
        ((crossLift m wd thickSheet thinSheet setup false false).stablePath = rowR m wd ∧
          (crossLift m wd thickSheet thinSheet setup false true).stablePath = rowT m wd)) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  have hNd := NonTrivalentValencyTwoRows.nonDanglingValency_anchor src
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlk hNd
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨Ends⟩ := NonTrivalentValencyTwoStarCountAll.nonempty_vanishingEnds m wd src hOrd
  have hEnds := anchorEnds_base m wd Ends
  have hGauged := gaugedData_valid (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
    anchorBlk thickSheet thinSheet (NonTrivalentValencyTwoTracks.wallValid m wd)
  exact ⟨typeChangeLink_of_prescribedBaseOneMove m wd thickSheet thinSheet setup hGauged hOrd
    src labelling₀ hRowVal hMatrixWall hEnds
    (prescribedBaseOneMove_of_unordered_rows m wd thickSheet thinSheet setup hA1)⟩

/-- **The Base I link at a Configuration A cross pair, with the two members named by
direction.**  `P` lies over `star.edge 0`, `Q` over `star.edge 1`, they have equal
dilation indices, and their incoming rows are the two rows the move names.  The
`t₃`-alignment gauge of `NonTrivalentValencyTwoGauge` turns the two index equalities
into a Base I setup;
`crossPair_identification` says the pair the setup puts at `A₁` is `{P, Q}` or the
complementary pair, and in the second case the same construction discharges the move
read from the other end of the contracted edge (`MoveData.swap`), whose own pair is
exactly the complementary one. -/
theorem link_of_crossPair_oriented (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hsplit : ∀ direction : Fin 2,
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        direction).card = 2)
    (P Q : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hPi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) P.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hQi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) Q.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hP : (⟨P.1, hPi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 0)
    (hQ : (⟨Q.1, hQi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 1)
    (hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex P.1 =
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex Q.1)
    (hrows : (survRow m wd P = rowT m wd ∧ survRow m wd Q = rowR m wd) ∨
      (survRow m wd P = rowR m wd ∧ survRow m wd Q = rowT m wd)) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  have hConn : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Connected :=
    (NonTrivalentValencyTwoTracks.wallValid m wd).1
  have hNd := NonTrivalentValencyTwoRows.nonDanglingValency_anchor src
  obtain ⟨R, hR, hRne⟩ := other_of_pair (hsplit 0) hP
  obtain ⟨S, hS, hSne⟩ := other_of_pair (hsplit 1) hQ
  -- the second index equality, from the two direction sums
  have hIndexSecond : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex R.1 =
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex S.1 := by
    have h0 := src.direction_index_sum 0
    have h1 := src.direction_index_sum 1
    rw [directionSurvivors_eq_pair (hsplit 0) hP hR (Ne.symm hRne),
      Finset.sum_pair (Ne.symm hRne)] at h0
    rw [directionSurvivors_eq_pair (hsplit 1) hQ hS (Ne.symm hSne),
      Finset.sum_pair (Ne.symm hSne)] at h1
    have hPQ : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex
          (⟨P.1, hPi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ anchorBlk)).1 =
        (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex
          (⟨Q.1, hQi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ anchorBlk)).1 := hk
    rw [hPQ] at h0
    have hZ : ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex R.1 : ℤ) =
        ((contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex S.1 : ℤ) := by
      linarith [h0, h1]
    exact_mod_cast hZ
  -- the gauged Base I setup and the two pair conjuncts
  obtain ⟨setup, -, -, -, -, -, -, hPairFirst, hPairSecond⟩ :=
    exists_gauged_candidate_of_contraction' wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) (wd.hCompat m) wallStar anchorBlk hNd hsplit ⟨P.1, hPi⟩ R ⟨Q.1, hQi⟩ S
      hP hR hQ hS (Ne.symm hRne) (Ne.symm hSne) hk hIndexSecond
  rcases crossPair_identification (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk hConn hsplit hP hR hQ hS (Ne.symm hRne) (Ne.symm hSne) setup hPairFirst
      hPairSecond with ⟨hT, hN⟩ | ⟨hT, hN⟩
  · -- the move's own pair sits at `A₁`
    have e0 := crossLift_stablePath_eq_survRow m wd _ _ setup false false P
      (congrArg Subtype.val hT)
    have e1 := crossLift_stablePath_eq_survRow m wd _ _ setup false true Q
      (congrArg Subtype.val hN)
    refine link_of_gauged_setup m wd wallStar anchorBlk src _ _ setup ?_
    rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨e0.trans ha, e1.trans hb⟩
    · exact Or.inr ⟨e0.trans ha, e1.trans hb⟩
  · -- the complementary pair sits at `A₁`: read the move from the other end
    have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
      wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
      wd.hRows wd.hZeroCoord anchorBlk hNd
    obtain ⟨Ends⟩ := NonTrivalentValencyTwoStarCountAll.nonempty_vanishingEnds m wd src hOrd
    have hEnds := anchorEnds_base m wd Ends
    have hRnd : ¬ IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne) R.1 :=
      NonTrivalentValencyTwoRows.survivor_not_isDangling hR
    have hSnd : ¬ IsDangling (contractDatum wd.cover wd.hc wd.hab wd.hOne) S.1 :=
      NonTrivalentValencyTwoRows.survivor_not_isDangling hS
    have hPt : P.1.1.1 = wallStar.edge 0 := survivor_target hP
    have hQt : Q.1.1.1 = wallStar.edge 1 := survivor_target hQ
    have hRt : R.1.1.1 = wallStar.edge 0 := survivor_target hR
    have hSt : S.1.1.1 = wallStar.edge 1 := survivor_target hS
    have hzo : wallStar.edge 0 ≠ wallStar.edge 1 := wallStar.edge_injective.ne (by decide)
    have hcross : ∀ x y : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne),
        x.1.1.1 = wallStar.edge 0 → y.1.1.1 = wallStar.edge 1 → x ≠ y := by
      intro x y hx hy hxy
      exact hzo (by rw [← hx, ← hy, hxy])
    have hPR : P ≠ (⟨R.1, hRnd⟩ :
        NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) := by
      intro hbad
      exact hRne (Subtype.ext (congrArg Subtype.val hbad).symm)
    have hQS : Q ≠ (⟨S.1, hSnd⟩ :
        NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) := by
      intro hbad
      exact hSne (Subtype.ext (congrArg Subtype.val hbad).symm)
    have hcomp := rows_of_complement m wd src hOrd hEnds P Q ⟨R.1, hRnd⟩ ⟨S.1, hSnd⟩
      hPi hQi R.2 S.2 (hcross P Q hPt hQt) hPR (hcross P ⟨S.1, hSnd⟩ hPt hSt)
      ((hcross ⟨R.1, hRnd⟩ Q hRt hQt).symm) hQS (hcross ⟨R.1, hRnd⟩ ⟨S.1, hSnd⟩ hRt hSt) hrows
    have e0 := crossLift_stablePath_eq_survRow m wd _ _ setup false false
      (⟨R.1, hRnd⟩ : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
      (congrArg Subtype.val hT)
    have e1 := crossLift_stablePath_eq_survRow m wd _ _ setup false true
      (⟨S.1, hSnd⟩ : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
      (congrArg Subtype.val hN)
    have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    refine (link_of_gauged_setup m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL)
      wallStar anchorBlk src _ _ setup ?_).map
      (NonTrivalentValencyFourDispatcher.linkOfSwap m wd hL)
    rcases hcomp with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨e0.trans ha, e1.trans hb⟩
    · exact Or.inl ⟨e0.trans ha, e1.trans hb⟩

/-- **The Base I link at a Configuration A cross pair.**  Neither member is named by
direction: the two survivors lie over different target occurrences, so one lies over
each direction of the incoming two-valent star. -/
theorem link_of_crossPair (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hsplit : ∀ direction : Fin 2,
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        direction).card = 2)
    (hg : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hg' : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hne : (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) ≠ g'.1.1.1)
    (hrows : (survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
      (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd))
    (hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 =
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  have hgd : (⟨g.1, hg⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          ⟨g.1, hg⟩) :=
    (mem_directionSurvivors _ _ _ _ _).mpr
      ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g.2, (edge_survivorLabel _ _ _ _).symm⟩
  have hg'd : (⟨g'.1, hg'⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          ⟨g'.1, hg'⟩) :=
    (mem_directionSurvivors _ _ _ _ _).mpr
      ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g'.2, (edge_survivorLabel _ _ _ _).symm⟩
  have hdne : survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g.1, hg⟩ ≠
      survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'⟩ := by
    intro hbad
    refine hne ?_
    rw [← edge_survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g.1, hg⟩,
      ← edge_survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'⟩, hbad]
  have hcase : ∀ d : Fin 2, d = 0 ∨ d = 1 := by decide
  rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      ⟨g.1, hg⟩) with hd | hd
  · rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'⟩) with hd' | hd'
    · exact absurd (hd.trans hd'.symm) hdne
    · rw [hd] at hgd
      rw [hd'] at hg'd
      exact link_of_crossPair_oriented m wd wallStar anchorBlk src hsplit g g' hg hg' hgd hg'd
        hk hrows
  · rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'⟩) with hd' | hd'
    · rw [hd] at hgd
      rw [hd'] at hg'd
      refine link_of_crossPair_oriented m wd wallStar anchorBlk src hsplit g' g hg' hg hg'd hgd
        hk.symm ?_
      rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hb, ha⟩
    · exact absurd (hd.trans hd'.symm) hdne

/-- **(H-BaseI) discharged: the Base I half of the cross-pair hypothesis of
`NonTrivalentValencyTwoDispatcher`.** -/
theorem baseOneCrossLink (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    NonTrivalentValencyTwoDispatcher.BaseOneCrossLink m wd h2 :=
  fun blk g g' src hsplit hg hg' hne hrows hk ↦
    link_of_crossPair m wd (TwoStar.of_card h2) blk g g' src hsplit hg hg' hne hrows hk

/-- **(H-cross) from the split half alone.** -/
theorem crossPairLink_of_splitCrossLink (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (hSplit : NonTrivalentValencyTwoDispatcher.SplitCrossLink m wd h2) :
    NonTrivalentValencyTwoDispatcher.CrossPairLink m wd h2 :=
  NonTrivalentValencyTwoDispatcher.crossPairLink_of_index_dichotomy m wd h2
    (baseOneCrossLink m wd h2) hSplit

/-- **`OuterWalk.TypeChangeLink` at every two-valent wall from the split half alone.** -/
theorem typeChangeLink_two_of_splitCrossLink (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (hSplit : NonTrivalentValencyTwoDispatcher.SplitCrossLink m wd h2) :
    Nonempty (TypeChangeLink m wd) :=
  NonTrivalentValencyTwoDispatcher.typeChangeLink_two m wd h2
    (crossPairLink_of_splitCrossLink m wd h2 hSplit)

/-! ## The split half of the cross pair -/

section Split

open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitExit (relabelStar
  directionSurvivors_relabelStar_zero directionSurvivors_relabelStar_one
  twoBranchAnchor_relabelStar split_relabelStar ordinaryTrivalent_splitGauged)

variable (m : graph.MoveData) {arrival : FacetArrival deg graph label (label m.base)}
  (wd : WallData arrival)
  (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
  (anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)

/-- The split analogue of `crossLift_stablePath_eq_survRow`. -/
theorem splitLift_stablePath_eq_survRow (thickSheet thinSheet : Fin deg)
    (ra : NonTrivalentValencyTwoSplitRows.SplitAnchor
      (NonTrivalentValencyTwoSplitGauge.splitGaugedData
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet)
      wallStar
      (NonTrivalentValencyTwoSplitGauge.splitGaugedAnchor
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet))
    (which : Bool) (e : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (h : (NonTrivalentValencyTwoSplitTracks.ungaugeSurvivor
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet
        (NonTrivalentValencyTwoSplitTracks.splitSurvivor m wd thickSheet thinSheet ra
          which)).1 = e.1) :
    (NonTrivalentValencyTwoSplitTracks.splitLift m wd thickSheet thinSheet ra which).stablePath =
      survRow m wd e := by
  have hEq : NonTrivalentValencyTwoSplitTracks.splitWallEdge m wd thickSheet thinSheet ra
      which = e := Subtype.ext h
  rw [NonTrivalentValencyTwoSplitTracks.splitLift_stablePath m wd thickSheet thinSheet ra
    which, hEq]
  rfl

/-- **The split link from a gauged split anchor whose pair at `S` carries the two rows
the move names.**  The star count of `NonTrivalentValencyTwoSplitStarCount` with
(H-split) discharged: the survivor clause
of `PrescribedSplitMove` does not order the pair, so either assignment works. -/
theorem link_of_splitAnchor
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (thickSheet thinSheet : Fin deg)
    (ra : NonTrivalentValencyTwoSplitRows.SplitAnchor
      (NonTrivalentValencyTwoSplitGauge.splitGaugedData
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet)
      wallStar
      (NonTrivalentValencyTwoSplitGauge.splitGaugedAnchor
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet))
    (A Dl : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hA : (NonTrivalentValencyTwoSplitTracks.ungaugeSurvivor
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet
      ra.alphaEdge).1 = A.1)
    (hD : (NonTrivalentValencyTwoSplitTracks.ungaugeSurvivor
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet
      ra.deltaEdge).1 = Dl.1)
    (hrows : (survRow m wd A = rowT m wd ∧ survRow m wd Dl = rowR m wd) ∨
      (survRow m wd A = rowR m wd ∧ survRow m wd Dl = rowT m wd)) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  have hNd := NonTrivalentValencyTwoRows.nonDanglingValency_anchor src
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlk hNd
  have hValid := NonTrivalentValencyTwoTracks.wallValid m wd
  have hGauged := NonTrivalentValencyTwoSplitGauge.splitGaugedData_valid
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet hValid
  have hOrdGauged := ordinaryTrivalent_splitGauged
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk thickSheet thinSheet
    hValid.1 hOrd
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨Ends⟩ := NonTrivalentValencyTwoStarCountAll.nonempty_vanishingEnds m wd src hOrd
  have hEnds := anchorEnds_base m wd Ends
  have e0 := splitLift_stablePath_eq_survRow m wd wallStar anchorBlk thickSheet thinSheet ra
    false A hA
  have e1 := splitLift_stablePath_eq_survRow m wd wallStar anchorBlk thickSheet thinSheet ra
    true Dl hD
  refine ⟨NonTrivalentValencyTwoSplitStarCount.typeChangeLink_of_prescribedSplitMove m wd
    thickSheet thinSheet ra hGauged hOrdGauged hOrd src labelling₀ hRowVal hMatrixWall hEnds
    ⟨⟨rfl, rfl⟩, ?_⟩⟩
  rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨coverDart m wd (thirdBase m), coverDart m wd m.right, (e0.trans ha).symm,
      (e1.trans hb).symm, ?_⟩
    rw [movedStar_base m, dart_coverDart, dart_coverDart]
  · refine ⟨coverDart m wd m.right, coverDart m wd (thirdBase m), (e0.trans ha).symm,
      (e1.trans hb).symm, ?_⟩
    rw [movedStar_base m, dart_coverDart, dart_coverDart,
      Finset.pair_comm (thirdBase m) m.right]

/-- **The split link at a Configuration A cross pair with the splitting member named.**
`A` lies over `star.edge 0`, `Dl` over `star.edge 1`, and `k_delta < k_alpha` (as in
Part II's subcase `{v2-nd4-t3-k2<k3}`: exactly the case in which the Base I member
does not exist). -/
theorem link_of_splitPair_oriented
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hsplit : ∀ direction : Fin 2,
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        direction).card = 2)
    (A Dl : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hAi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) A.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hDi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) Dl.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hA : (⟨A.1, hAi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 0)
    (hD : (⟨Dl.1, hDi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 1)
    (hIdx : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex Dl.1 <
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex A.1)
    (hrows : (survRow m wd A = rowT m wd ∧ survRow m wd Dl = rowR m wd) ∨
      (survRow m wd A = rowR m wd ∧ survRow m wd Dl = rowT m wd)) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  obtain ⟨B, hB, hBne⟩ := other_of_pair (hsplit 0) hA
  obtain ⟨Eps, hEps, hEpsNe⟩ := other_of_pair (hsplit 1) hD
  have hValid := NonTrivalentValencyTwoTracks.wallValid m wd
  refine link_of_splitAnchor m wd wallStar anchorBlk src _ _
    (NonTrivalentValencyTwoSplitRows.splitAnchor_gauged src hsplit
      (NonTrivalentUniqueFourValent.wall_target_connected wd.cover wd.fullDim wd.hab wd.hOne)
      (NonTrivalentUniqueFourValent.wall_target_genus wd.cover wd.fullDim wd.hab wd.hOne)
      hValid.1 hA hB hD hEps (Ne.symm hBne) (Ne.symm hEpsNe) hIdx) A Dl ?_ ?_ hrows
  · exact congrArg Subtype.val
      ((NonTrivalentValencyTwoSplitGauge.splitSurvivorEquiv
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk _ _).symm_apply_apply _)
  · exact congrArg Subtype.val
      ((NonTrivalentValencyTwoSplitGauge.splitSurvivorEquiv
        (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk _ _).symm_apply_apply _)

/-- The same with only the two directions named: the strict index inequality picks the
member, and when it points the other way the mirror member
(`NonTrivalentValencyTwoSplitExit.relabelStar`) realises the pairing. -/
theorem link_of_splitPair_dir
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hsplit : ∀ direction : Fin 2,
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        direction).card = 2)
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hgi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hg'i : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hgd : (⟨g.1, hgi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 0)
    (hg'd : (⟨g'.1, hg'i⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 1)
    (hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 ≠
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1)
    (hrows : (survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
      (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd)) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  have hz : directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (relabelStar wallStar) anchorBlk 0 =
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 1 :=
    directionSurvivors_relabelStar_zero wallStar
  have ho : directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (relabelStar wallStar) anchorBlk 1 =
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk 0 :=
    directionSurvivors_relabelStar_one wallStar
  rcases lt_or_gt_of_ne hk with hlt | hlt
  · refine link_of_splitPair_oriented m wd (relabelStar wallStar) anchorBlk
      (twoBranchAnchor_relabelStar src) (split_relabelStar hsplit) g' g hg'i hgi ?_ ?_ hlt ?_
    · rw [hz]
      exact hg'd
    · rw [ho]
      exact hgd
    · rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hb, ha⟩
  · exact link_of_splitPair_oriented m wd wallStar anchorBlk src hsplit g g' hgi hg'i hgd hg'd
      hlt hrows

/-- **The split link at a Configuration A cross pair.**  Neither member is named by
direction; the two survivors lie over different target occurrences, so one lies over
each direction. -/
theorem link_of_splitPair
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
    (hsplit : ∀ direction : Fin 2,
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        direction).card = 2)
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hgi : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hg'i : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk))
    (hne : (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) ≠ g'.1.1.1)
    (hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 ≠
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1)
    (hrows : (survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
      (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd)) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  have hgd : (⟨g.1, hgi⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          ⟨g.1, hgi⟩) :=
    (mem_directionSurvivors _ _ _ _ _).mpr
      ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g.2, (edge_survivorLabel _ _ _ _).symm⟩
  have hg'd : (⟨g'.1, hg'i⟩ : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk)) ∈
      directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
          ⟨g'.1, hg'i⟩) :=
    (mem_directionSurvivors _ _ _ _ _).mpr
      ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g'.2, (edge_survivorLabel _ _ _ _).symm⟩
  have hdne : survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g.1, hgi⟩ ≠
      survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'i⟩ := by
    intro hbad
    refine hne ?_
    rw [← edge_survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g.1, hgi⟩,
      ← edge_survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        ⟨g'.1, hg'i⟩, hbad]
  have hcase : ∀ d : Fin 2, d = 0 ∨ d = 1 := by decide
  rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      ⟨g.1, hgi⟩) with hd | hd
  · rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk ⟨g'.1, hg'i⟩) with hd' | hd'
    · exact absurd (hd.trans hd'.symm) hdne
    · rw [hd] at hgd
      rw [hd'] at hg'd
      exact link_of_splitPair_dir m wd wallStar anchorBlk src hsplit g g' hgi hg'i hgd hg'd
        hk hrows
  · rcases hcase (survivorLabel (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlk ⟨g'.1, hg'i⟩) with hd' | hd'
    · rw [hd] at hgd
      rw [hd'] at hg'd
      refine link_of_splitPair_dir m wd wallStar anchorBlk src hsplit g' g hg'i hgi hg'd hgd
        (Ne.symm hk) ?_
      rcases hrows with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hb, ha⟩
    · exact absurd (hd.trans hd'.symm) hdne

end Split

/-- **(H-split) discharged: the split half of the cross-pair hypothesis of
`NonTrivalentValencyTwoDispatcher`.** -/
theorem splitCrossLink (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    NonTrivalentValencyTwoDispatcher.SplitCrossLink m wd h2 :=
  fun blk g g' src hsplit hg hg' hne hrows hk ↦
    link_of_splitPair m wd (TwoStar.of_card h2) blk src hsplit g g' hg hg' hne hk hrows

/-- **(H-cross) discharged.**  By the closing count of Part II's valency-two analysis,
exactly one of the Base I member and the Configuration A split member realises each
cross pairing, and both are constructed. -/
theorem crossPairLink (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    NonTrivalentValencyTwoDispatcher.CrossPairLink m wd h2 :=
  NonTrivalentValencyTwoDispatcher.crossPairLink_of_index_dichotomy m wd h2
    (baseOneCrossLink m wd h2) (splitCrossLink m wd h2)

/-- **`OuterWalk.TypeChangeLink` at every two-valent wall, with no hypothesis.** -/
theorem link_two (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    Nonempty (TypeChangeLink m wd) :=
  NonTrivalentValencyTwoDispatcher.typeChangeLink_two m wd h2 (crossPairLink m wd h2)

/-- The same in the shape the `link` binder asks for. -/
def typeChangeLink_two' (m : graph.MoveData)
    {arrival : FacetArrival deg graph label (label m.base)} (wd : WallData arrival)
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    TypeChangeLink m wd :=
  (link_two m wd h2).some

end Headline

/-! ## The walk's `link` binder from `SplitCrossLink` alone -/

section Dispatch

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **The `link` binder of `OuterWalk.coneEntry_of_reaches` with every branch
discharged except the Configuration A split cross pair.** -/
def link_of_splitCrossLink {G : CubicDartGraph D V}
    (hSplit : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival)
        (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 2),
        NonTrivalentValencyTwoDispatcher.SplitCrossLink m wd h2) :
    ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival), TypeChangeLink m wd :=
  NonTrivalentValencyThreeDispatcher.link_of_valency_two
    (fun K hK m arrival wd h2 ↦
      NonTrivalentValencyTwoDispatcher.typeChangeLink_of_valency_two m wd h2
        (crossPairLink_of_splitCrossLink m wd h2 (hSplit K hK m arrival wd h2)))

/-- **The `link` binder of `OuterWalk.coneEntry_of_reaches`, with NO hypothesis.**
`NonTrivalentValencyFourDispatcher` handles valency four,
`NonTrivalentValencyThreeDispatcher` valency three, `NonTrivalentValencyTwoDispatcher`
reduces valency two to the cross pair, and both halves of the cross pair are discharged
here. -/
def link_all {G : CubicDartGraph D V} :
    ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival), TypeChangeLink m wd :=
  NonTrivalentValencyThreeDispatcher.link_of_valency_two
    (fun _ _ m _ wd h2 ↦ typeChangeLink_two' m wd h2)

end Dispatch

end

end DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneLink
