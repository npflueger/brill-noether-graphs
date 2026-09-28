import DraismaVargas.LocalCases.MoveMirror
import DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleStarCount
import DraismaVargas.LocalCases.NonTrivalentValencyFourDispatcher

/-!
# The valency-three move-to-type dispatcher: `TypeChangeLink m wd` for every move

Source: Vargas, Part II, Section 5.1 (the labelling convention (1) at a
non-trivalent wall, and the three combinatorial resolutions of `H_0` listed
under *Graphs contracting to `H_0`*) and Section 5.3, case `{v3-nd4}` (the
doubled direction `t_2` carries the two survivors `e_2`, `e_5`, the two simple
directions `t_3`, `t_4` carry `e_3`, `e_4`, and the three `2+2` partitions of
`{e_2, e_3, e_4, e_5}` are Type III `{e_2,e_5}|{e_3,e_4}`, Type I
`{e_2,e_3}|{e_4,e_5}` and Type II `{e_2,e_4}|{e_3,e_5}`; the paragraph on the
base trees `T_α`, `α ∈ {3, 4}`, describes the Type I/II resolution, whose
`SimpleBase` inequality `k_beta + k_delta <= |A|` singles out one of the two
complementary realisations of each simple partition), together with
Draisma--Vargas Part I's definition of non-dangling valency and its
limit-matrix lemma (`lemma-limit-matrix-change`).  At a three-valent wall the
incoming cover may carry a *pass-through* survivor, so the (H-*) conditions are
row-level, and every prescribed pair straddles the two ends of the vanishing
occurrence.

The vertex dictionary and (H-III) are in `NonTrivalentValencyThreeTracks`, the
Type III star count in `NonTrivalentValencyThreeStarCount`, the vertex
dictionary and (H-I/II) of Types I/II in `NonTrivalentValencyThreeSimpleTracks`,
and the Types I/II star count in `NonTrivalentValencyThreeSimpleStarCount`.
With the survivor clauses stated at row level
(`prescribedDoubledMove_of_rows`, `prescribedSimpleMove_of_rows`), the link at a
three-valent wall follows from (H-III) or (H-I/II) and the wall star alone.
This module discharges those conditions from the move itself and therefore
delivers the link at **every** wall datum of surviving valency three with no
hypothesis beyond `card (incidentEdges <wd.a, wd.hab>) = 3`.

## The problem, and the shape of the solution

A Whitehead move `m` puts at `graph.vert m.base` one row from each end of the
vanishing occurrence (`MoveMirror.movedStar_eq_pair`: the moved star is
`{m.base, thirdLeft m, m.right}`).  The (H-*) conditions name a *specific*
pair of anchor survivors, and each candidate family realises only one of the two
complementary pairs of its own partition -- at Types I/II because `SimpleBase`
carries `k_beta + k_delta <= |A|`, and the four survivor indices sum to
`2|A| + 1` (`ThreeBranchAnchor.survivor_index_sum`), so exactly one of the two
complementary realisations exists.  `MoveData.swap` cannot repair this: it
toggles the orientation clause and the pair at `graph.vert m.base` together.
The repair is `MoveMirror.mirror`: `graph.move (mirror m)` is
isomorphic to `graph.move m` by a label-preserving isomorphism, and `mirror m`
puts the complementary pair at `graph.vert m.base`
(`MoveMirror.movedStar_mirror_eq_pair`).

## What is proved

### 1.  The row census at the two ends (Sections 1--5)

* `incidenceCount_anchor_eq_ends`: **(T2) at the anchor without any hypothesis on
  the anchor fibre.**  For every retained row `r` of the wall datum, the star of
  `r` at the merged anchor is the disjoint union of the incoming stars of
  `incomingRow r` at the two ends of the vanishing occurrence.
  `WallSplitIncidence.incidenceCount_anchor` proves this only under
  `activeFibreVertices A = {leftEnd, rightEnd}`, which a three-valent wall does
  *not* supply: the fibre may carry divalent pass-through vertices.  The proof
  here is the leftover equation -- a stable row meets the branch vertices twice
  in all on both sides of the wall (`sum_incidenceCount_branchVertex`), and away
  from the anchor the two censuses agree through the `hFibre`-free
  `NonTrivalentValencyThreeTracks.branchEquivAnchorComplement` and
  `NonTrivalentValencyThreeStarCount.incidenceCount_wall_eq_incoming`.
* `incidentEdges_anchor`, `incidenceCount_anchor_four`: the star of the anchor is
  exactly the four survivors `doubledND false`, `doubledND true`, `simpleND
  false`, `simpleND true`, which are pairwise distinct (two lie over the doubled
  target direction, one over each simple direction).
* `incidentEdges_leftEnd` / `_rightEnd`, `incidenceCount_leftEnd` / `_rightEnd`:
  each end of the vanishing occurrence is trivalent, and its star is the
  vanishing occurrence together with the occurrences of the two darts the two
  complementary moves read there -- `thirdLeft m`, `m.left` at the `A_u` end and
  `m.right`, `thirdRight m` at the `A_v` end.
* `keptRow`, `sentRow`, `broughtRow`, `stayedRow` and `census`: the four wall
  rows of those four darts, and **the census** -- with multiplicity they are the
  four rows of the anchor survivors.  `keptRow_mirror` and `broughtRow_mirror`
  say that the mirror move reads `sentRow` and `stayedRow`, the complementary
  pair.

### 2.  The classification and the links (Sections 6--8)

* `classify`: **the move-to-partition classification.**  The pair
  `{keptRow, broughtRow}` the move puts at `graph.vert m.base` is the doubled
  pair (Type III), or the simple pair, or one of each (Types I/II); and in the
  last two cases the complementary pair `{sentRow, stayedRow}` -- which is what
  the mirror move puts there -- is the complementary pair of survivors.  The
  proof is pure counting from `census` plus `pair_of_count_eq`; rows of distinct
  survivors may coincide, so nothing here speaks of "the survivor with row `r`".
* `simpleBaseOf`, `Realisable`, `realisable_or`: the Types I/II base with
  `alphaLabel = simpleLabel i` and the doubled survivor `j` at `A_u`, its
  realisability inequality, and **the dichotomy**: exactly one of the two
  complementary realisations of a simple partition satisfies it, because the
  four survivor indices sum to `2|A| + 1` (`sum_index_four`).
* `link_of_doubled`, `link_of_simple`: the link in each case, from
  `prescribedDoubledMove_of_rows` / `prescribedSimpleMove_of_rows` and the star
  counts of `NonTrivalentValencyThreeStarCount` and
  `NonTrivalentValencyThreeSimpleStarCount`.
* `nonempty_typeChangeLink_of_orientation`: the link at a three-valent wall whose
  vanishing occurrence is oriented with its `A_u` end at `graph.vert m.base`,
  using `MoveMirror.linkOfMirror` in the two cases where the pair the move names
  is the complement of the realisable one.
* `dart_facetDartLeft_cases_three`, `facetRow_swap_three`, `facetEdge_swap_three`,
  `facetDartLeft_swap_three`: the orientation is normalised by
  `CubicDarts.MoveData.swap` exactly as at valency four, reusing
  `NonTrivalentValencyFourDispatcher`'s `swapArrival`, `swapWallData` and
  `linkOfSwap`.
* `typeChangeLink_three`, `typeChangeLink_three'`: **`OuterWalk.TypeChangeLink` at
  every three-valent wall datum of every Whitehead move, from
  `card (incidentEdges <wd.a, wd.hab>) = 3` alone**; the anchor data are produced
  internally by `NonTrivalentValencyThreeExit.exists_anchor_of_wallData`.
* `typeChangeLink_of_valency_two`, `link_of_valency_two`: the valency dispatcher
  and the `link` binder of `OuterWalk.coneEntry_of_reaches` with the four-valent
  (`NonTrivalentValencyFourDispatcher`) and three-valent branches discharged,
  taking the valency-two exit as an explicit parameter.
  (`NonTrivalentValencyTwoBaseOneLink.link_all` inhabits `link` with no
  hypothesis at all, valency two included.)

## Why every move at a three-valent wall is covered

The pair a move puts at `graph.vert m.base` straddles the two ends, so it is one
of the four "one from each end" pairs; by `census` its rows are the rows of two
of the four anchor survivors, and the three `2+2` partitions of those four are
exactly Types III, I and II.  A move never prescribes the *incoming* partition: the
pair it names has one member at each end, while the incoming partition has both
members of each class at one end.  There is also no "trivial move" to worry
about -- `(graph.move m).vert m.left = graph.vert (graph.op m.base)` differs from
`graph.vert m.left = graph.vert m.base` by `MoveData.nonloop`, so
`graph.move m <> graph` always -- and in any case nothing below uses that the
type changes: `classify` reads only which pair of rows the move places at
`graph.vert m.base`, and all four such pairs are covered.  In each case one of
the two complementary realisations of the resulting partition exists
(`realisable_or` for Types I/II, unconditionally for Type III), and the mirror
move supplies the other.

## The hypotheses that remain explicit

1. `h3 : card (incidentEdges <wd.a, wd.hab>) = 3`.  Nothing else: `wallStar`,
   `anchorBlk`, `src`, `hNoGlue`, `hValid`, the partition and the base are all
   produced here, so the three-valent branch of the `link` binder is **closed**.
2. The valency-two branch.  `link_of_valency_two` names it as an explicit
   parameter; `NonTrivalentValencyTwoBaseOneLink.link_all` discharges it
   unconditionally.
3. No claim is made that the outgoing type computed here is the one the paper's
   count would assign: existence of *a* prescribed resolution realised by the
   move is all the walk needs.

No structure is introduced.  `Realisable` is a `Prop` abbreviation of the
`SimpleBase` field, with `realisable_or` as its non-vacuity witness (one of the
two complementary instances always holds); `simpleBaseOf` inhabits
`NonTrivalentValencyThreeSimpleCandidate.SimpleBase`, and `simpleSur`,
`doubledSur`, `simpleND`, `doubledND`, `coverDart`, `endWallRow`, `keptRow`,
`sentRow`, `broughtRow`, `stayedRow` name objects of data already in hand, each
used in the theorems above.

## Used by

The `link` binder of `OuterWalk.coneEntry_of_reaches`, hence
`StatementFromLink.nonempty_evenSubdivisionPencil_of_link`, at Part II case
`{v3-nd4}`; and the final valency dispatcher, through `link_of_valency_two`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeDispatcher


open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeTracks
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.MoveMirror

noncomputable section

section Census

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)

/-- The incoming row of a retained row of the wall datum. -/
def inRow (r : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) : StablePath wd.cover :=
  StablePathFacetContraction.incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hCompat m) (wd.hForest m) r

theorem stablePath_liftEdge'
    (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (liftEdge m wd g).stablePath = inRow m wd g.stablePath := rfl

include wallStar in
theorem inRow_injective : Function.Injective (inRow m wd) :=
  NonTrivalentValencyThreeStarCount.injective_incomingRow m wd wallStar

theorem inRow_ne_facetRow (r : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    inRow m wd r ≠ facetRow m wd :=
  StablePathFacetContraction.incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hCompat m) (wd.hForest m) wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord
    wd.hFacetZero r

theorem exists_inRow (ρ : StablePath wd.cover) (h : ρ ≠ facetRow m wd) :
    ∃ r, inRow m wd r = ρ :=
  StablePathFacetContraction.exists_incomingRow_eq wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hCompat m) (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord ρ h

include wallStar in
/-- **`HasPathEnds` of the wall datum at a three-valent wall.**  No-return comes
from the wall star alone
(`NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar`). -/
theorem hasPathEnds_wallDatum :
    HasPathEnds (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  WallDatumPathEnds.hasPathEnds_contractDatum wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hForest m) wd.coordinates (label m.base)
    (LeafFacetNoReturn.noContractedReturnOffRow_of_noContractedReturn wd.cover wd.contracted
      (wd.fullDim.labelling.row.symm (label m.base))
      (NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar wd.cover wd.fullDim
        wd.hc wd.hab wd.hOne wallStar))
    wd.hZeroCoord wd.hPosCoord wd.hFacetZero

variable (src : ThreeBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hValid : (contractDatum wd.cover wd.hc wd.hab wd.hOne).Valid)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum wd.cover wd.hc wd.hab wd.hOne))

include src hValid in
/-- **(T2) at the anchor: the star of a retained row at the merged anchor is the
disjoint union of the incoming stars at the two ends of the vanishing
occurrence.**  Unlike `WallSplitIncidence.incidenceCount_anchor` this needs no
hypothesis on the anchor fibre -- which is what a three-valent wall cannot
supply, because the fibre may carry divalent pass-through vertices.  The proof
is the leftover equation: a stable row meets the branch vertices twice in all,
on both sides of the wall, and away from the anchor the two censuses agree
through `NonTrivalentValencyThreeTracks.branchEquivAnchorComplement`. -/
theorem incidenceCount_anchor_eq_ends
    (r : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (anchorVertex m wd anchorBlk) r =
      incidenceCount wd.cover (leftEnd m wd) (inRow m wd r) +
        incidenceCount wd.cover (rightEnd m wd) (inRow m wd r) := by
  classical
  set A : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
    ⟨anchorVertex m wd anchorBlk, by
      rw [nonDanglingValency_anchorVertex m wd src]; omega⟩ with hA
  set L : BranchVertex wd.cover := leftBranch m wd wallStar with hL
  set R : BranchVertex wd.cover := rightBranch m wd wallStar with hR
  have hLR : L ≠ R := fun h ↦ leftEnd_ne_rightEnd m wd (congrArg Subtype.val h)
  have hSumW := NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) hValid.1
    (hasPathEnds_wallDatum m wd wallStar) r
  have hSumC := NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex
    wd.cover wd.fullDim.connected wd.fullDim.pathEnds (inRow m wd r)
  have hkey : ∑ v ∈ Finset.univ.erase A,
        incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) v.1 r =
      ∑ v ∈ (Finset.univ.erase L).erase R, incidenceCount wd.cover v.1 (inRow m wd r) := by
    have hsubW : ∀ x : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne),
        x ∈ Finset.univ.erase A ↔ x.1 ≠ anchorVertex m wd anchorBlk := by
      intro x
      rw [Finset.mem_erase]
      constructor
      · rintro ⟨hne, -⟩
        exact fun h ↦ hne (Subtype.ext h)
      · intro h
        exact ⟨fun hbad ↦ h (congrArg Subtype.val hbad), Finset.mem_univ _⟩
    have hsubC : ∀ x : BranchVertex wd.cover,
        x ∈ (Finset.univ.erase L).erase R ↔ (x.1 ≠ leftEnd m wd ∧ x.1 ≠ rightEnd m wd) := by
      intro x
      rw [Finset.mem_erase, Finset.mem_erase]
      constructor
      · rintro ⟨hRne, hLne, -⟩
        exact ⟨fun h ↦ hLne (Subtype.ext h), fun h ↦ hRne (Subtype.ext h)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun hbad ↦ h2 (congrArg Subtype.val hbad),
          fun hbad ↦ h1 (congrArg Subtype.val hbad), Finset.mem_univ _⟩
    rw [Finset.sum_subtype _ hsubW, Finset.sum_subtype _ hsubC]
    refine (Fintype.sum_equiv
      (NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src)
      (fun v ↦ incidenceCount wd.cover v.1.1 (inRow m wd r))
      (fun w ↦ incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w.1.1 r)
      (fun v ↦ ?_)).symm
    exact (NonTrivalentValencyThreeStarCount.incidenceCount_wall_eq_incoming m wd wallStar src
      _ (NonTrivalentValencyThreeTracks.branchEquivAnchorComplement m wd wallStar src v).2
      v.1.1 rfl v.1.2 r).symm
  have hAsum := Finset.add_sum_erase Finset.univ
    (fun v : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ↦
      incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) v.1 r) (Finset.mem_univ A)
  have hLsum := Finset.add_sum_erase Finset.univ
    (fun v : BranchVertex wd.cover ↦ incidenceCount wd.cover v.1 (inRow m wd r))
    (Finset.mem_univ L)
  have hRmem : R ∈ Finset.univ.erase L :=
    Finset.mem_erase.mpr ⟨fun h ↦ hLR h.symm, Finset.mem_univ _⟩
  have hRsum := Finset.add_sum_erase (Finset.univ.erase L)
    (fun v : BranchVertex wd.cover ↦ incidenceCount wd.cover v.1 (inRow m wd r)) hRmem
  have hAval : incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) A.1 r =
      incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (anchorVertex m wd anchorBlk) r := rfl
  have hLval : incidenceCount wd.cover L.1 (inRow m wd r) =
      incidenceCount wd.cover (leftEnd m wd) (inRow m wd r) := rfl
  have hRval : incidenceCount wd.cover R.1 (inRow m wd r) =
      incidenceCount wd.cover (rightEnd m wd) (inRow m wd r) := rfl
  rw [hAval] at hAsum
  rw [hLval] at hLsum
  rw [hRval] at hRsum
  omega

/-! ## 2.  The four survivors at the anchor -/

section Survivors

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (source : ThreeBranchAnchor data star anchor)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- The two simple directions of the anchor, indexed by a `Bool`. -/
def simpleLabel (i : Bool) : Fin 3 :=
  if i then Prescribed.secondSimple source else Prescribed.firstSimple source

theorem simpleLabel_ne_doubled (i : Bool) :
    simpleLabel source i ≠ Prescribed.doubled source := by
  cases i
  · exact Prescribed.firstSimple_ne source
  · exact Prescribed.secondSimple_ne source

theorem simpleLabel_ne_simpleLabel (i : Bool) :
    simpleLabel source i ≠ simpleLabel source (!i) := by
  cases i
  · exact Prescribed.firstSimple_ne_secondSimple source
  · exact (Prescribed.firstSimple_ne_secondSimple source).symm

/-- The surviving occurrence of the `i`-th simple direction. -/
noncomputable def simpleSur (i : Bool) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  NonTrivalentValencyThreeSimpleCandidate.simpleSurvivor source (simpleLabel source i)
    (simpleLabel_ne_doubled source i)

/-- The surviving occurrence of the doubled direction chosen by `j`. -/
noncomputable def doubledSur (j : Bool) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  NonTrivalentValencyThreeSimpleCandidate.doubledSurvivor source j

theorem simpleSur_target (i : Bool) :
    (simpleSur source i).1.1.1 = directionEdge star (simpleLabel source i) :=
  ((mem_directionSurvivors data star anchor (simpleLabel source i) (simpleSur source i)).mp
    (NonTrivalentValencyThreeSimpleCandidate.simpleSurvivor_mem source (simpleLabel source i)
      (simpleLabel_ne_doubled source i))).2

theorem doubledSur_target (j : Bool) :
    (doubledSur source j).1.1.1 = directionEdge star (Prescribed.doubled source) :=
  ((mem_directionSurvivors data star anchor (Prescribed.doubled source)
    (doubledSur source j)).mp
      (NonTrivalentValencyThreeSimpleCandidate.doubledSurvivor_mem source j)).2

theorem simpleSur_survives (i : Bool) : ¬ IsDangling data (simpleSur source i).1 :=
  (W3R1SourceProfile.mem_survivors _ _ _).mp
    ((mem_directionSurvivors _ _ _ _ _).mp
      (NonTrivalentValencyThreeSimpleCandidate.simpleSurvivor_mem source (simpleLabel source i)
        (simpleLabel_ne_doubled source i))).1

theorem doubledSur_survives (j : Bool) : ¬ IsDangling data (doubledSur source j).1 :=
  (W3R1SourceProfile.mem_survivors _ _ _).mp
    ((mem_directionSurvivors _ _ _ _ _).mp
      (NonTrivalentValencyThreeSimpleCandidate.doubledSurvivor_mem source j)).1

/-- The `i`-th simple survivor as a surviving occurrence. -/
noncomputable def simpleND (i : Bool) : NonDanglingEdge data :=
  ⟨(simpleSur source i).1, simpleSur_survives source i⟩

/-- The `j`-th doubled survivor as a surviving occurrence. -/
noncomputable def doubledND (j : Bool) : NonDanglingEdge data :=
  ⟨(doubledSur source j).1, doubledSur_survives source j⟩

theorem simpleND_ne_doubledND (i j : Bool) : simpleND source i ≠ doubledND source j := by
  intro h
  refine simpleLabel_ne_doubled source i (directionEdge_injective star ?_)
  rw [← simpleSur_target source i, ← doubledSur_target source j]
  exact congrArg (fun e : NonDanglingEdge data ↦ (e.1.1.1 : target.edges)) h

theorem simpleND_ne_simpleND (i : Bool) : simpleND source i ≠ simpleND source (!i) := by
  intro h
  refine simpleLabel_ne_simpleLabel source i (directionEdge_injective star ?_)
  rw [← simpleSur_target source i, ← simpleSur_target source (!i)]
  exact congrArg (fun e : NonDanglingEdge data ↦ (e.1.1.1 : target.edges)) h

theorem doubledND_ne_doubledND (j : Bool) : doubledND source j ≠ doubledND source (!j) := by
  intro h
  exact NonTrivalentValencyThreeSimpleCandidate.doubledSurvivor_ne source j
    (Subtype.ext (congrArg (fun e : NonDanglingEdge data ↦ e.1) h))

/-- **The star of the anchor is exactly the four survivors.** -/
theorem incidentEdges_anchor :
    incidentEdges data (WallBlock.sourceVertex data wall anchor) =
      {doubledND source false, doubledND source true, simpleND source false,
        simpleND source true} := by
  classical
  have hd := doubledND_ne_doubledND source false
  have hs := simpleND_ne_simpleND source false
  have hsub : ({doubledND source false, doubledND source true, simpleND source false,
      simpleND source true} : Finset (NonDanglingEdge data)) ⊆
      incidentEdges data (WallBlock.sourceVertex data wall anchor) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rw [mem_incidentEdges]
    rcases he with rfl | rfl | rfl | rfl
    · exact (doubledSur source false).2
    · exact (doubledSur source true).2
    · exact (simpleSur source false).2
    · exact (simpleSur source true).2
  have hcard : ({doubledND source false, doubledND source true, simpleND source false,
      simpleND source true} : Finset (NonDanglingEdge data)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hd, fun h ↦ simpleND_ne_doubledND source false false h.symm,
          fun h ↦ simpleND_ne_doubledND source true false h.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨fun h ↦ simpleND_ne_doubledND source false true h.symm,
          fun h ↦ simpleND_ne_doubledND source true true h.symm⟩),
      Finset.card_insert_of_notMem (by simpa using hs), Finset.card_singleton]
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, card_incidentEdges, NonTrivalentValencyThreeRows.nonDanglingValency_anchor source]

/-- **The star count at the anchor, split over the four survivors.** -/
theorem incidenceCount_anchor_four (r : StablePath data) :
    incidenceCount data (WallBlock.sourceVertex data wall anchor) r =
      (if (doubledND source false).stablePath = r then 1 else 0) +
        (if (doubledND source true).stablePath = r then 1 else 0) +
        (if (simpleND source false).stablePath = r then 1 else 0) +
        (if (simpleND source true).stablePath = r then 1 else 0) := by
  classical
  rw [incidenceCount, incidentEdges_anchor source, Finset.card_filter,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨doubledND_ne_doubledND source false,
        fun h ↦ simpleND_ne_doubledND source false false h.symm,
        fun h ↦ simpleND_ne_doubledND source true false h.symm⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨fun h ↦ simpleND_ne_doubledND source false true h.symm,
        fun h ↦ simpleND_ne_doubledND source true true h.symm⟩),
    Finset.sum_insert (by simpa using simpleND_ne_simpleND source false),
    Finset.sum_singleton]
  ring

@[simp] theorem simpleLabel_false : simpleLabel source false = Prescribed.firstSimple source := rfl

@[simp] theorem simpleLabel_true : simpleLabel source true = Prescribed.secondSimple source := rfl

/-- **Identity (boxplus) of the source, in the `Bool`-indexed form**: the four
survivor indices sum to `2|A| + 1`. -/
theorem sum_index_four (i j : Bool) :
    NonTrivalentValencyThreeSimpleCandidate.directionIndex data star anchor
        (simpleLabel source i) +
      NonTrivalentValencyThreeSimpleCandidate.directionIndex data star anchor
        (simpleLabel source (!i)) +
      (data.sourceEdgeIndex (doubledSur source j).1 +
        data.sourceEdgeIndex (doubledSur source (!j)).1) =
      2 * (data.vertexPartition wall).blockCard anchor.1 + 1 := by
  have hbase : NonTrivalentValencyThreeSimpleCandidate.directionIndex data star anchor
        (Prescribed.doubled source) +
      NonTrivalentValencyThreeSimpleCandidate.directionIndex data star anchor
        (Prescribed.firstSimple source) +
      NonTrivalentValencyThreeSimpleCandidate.directionIndex data star anchor
        (Prescribed.secondSimple source) =
      2 * (data.vertexPartition wall).blockCard anchor.1 + 1 :=
    Prescribed.sum_directionSurvivors_index source
  have hd : NonTrivalentValencyThreeSimpleCandidate.directionIndex data star anchor
      (Prescribed.doubled source) =
      data.sourceEdgeIndex (Prescribed.firstDoubled source).1 +
        data.sourceEdgeIndex (Prescribed.secondDoubled source).1 :=
    NonTrivalentValencyThreeSimpleCandidate.directionIndex_doubled source false
  cases i <;> cases j <;>
    simp only [simpleLabel_false, simpleLabel_true, doubledSur, Bool.not_false, Bool.not_true,
      NonTrivalentValencyThreeSimpleCandidate.doubledSurvivor_false,
      NonTrivalentValencyThreeSimpleCandidate.doubledSurvivor_true] <;>
    omega

end Survivors

/-! ## 3.  The four darts at the two ends of the vanishing occurrence -/

/-- The dart of the incoming cover that the tracking sends to `d`. -/
def coverDart (d : D) : StableSourceDarts.Dart wd.cover := wd.tracks.iso.dart.symm d

@[simp] theorem dart_coverDart (d : D) : wd.tracks.iso.dart (coverDart m wd d) = d :=
  Equiv.apply_symm_apply _ _

theorem dart_ext {d₁ d₂ : StableSourceDarts.Dart wd.cover} (h₁ : d₁.1 = d₂.1)
    (h₂ : d₁.2.1 = d₂.2.1) : d₁ = d₂ := by
  revert h₁ h₂
  obtain ⟨v₁, e₁⟩ := d₁
  obtain ⟨v₂, e₂⟩ := d₂
  intro h₁ h₂
  dsimp only at h₁ h₂
  subst h₁
  exact congrArg _ (Subtype.ext h₂)

include wd in
/-- A dart other than the two darts of the contracted edge does not carry the
vanishing row. -/
theorem row_ne_facetRow (z : D) (h₁ : z ≠ m.base) (h₂ : z ≠ graph.op m.base) :
    (coverDart m wd z).2.1.stablePath ≠ facetRow m wd := by
  intro hBad
  have hlab : label z = label m.base := by
    have h := wd.tracks.row_map (coverDart m wd z)
    rw [dart_coverDart] at h
    rw [h]
    show wd.fullDim.labelling.row (coverDart m wd z).2.1.stablePath = label m.base
    rw [hBad]
    show wd.fullDim.labelling.row (wd.fullDim.labelling.row.symm (label m.base)) = label m.base
    exact Equiv.apply_symm_apply _ _
  have hmem : z ∈ (Finset.univ.filter fun d : D ↦ label d = label m.base) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlab⟩
  rw [NonTrivalentValencyFourDispatcher.filter_label_base m wd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact h₁ h
  · exact h₂ h

theorem coverDart_ne_facetEdge (z : D) (h₁ : z ≠ m.base) (h₂ : z ≠ graph.op m.base) :
    (coverDart m wd z).2.1 ≠ facetEdge m wd := by
  intro hBad
  exact row_ne_facetRow m wd z h₁ h₂ (by rw [hBad]; exact facetEdge_stablePath m wd)

include wallStar in
theorem coverDart_vertex_left (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (z : D) (hz : graph.vert z = graph.vert m.base) :
    (coverDart m wd z).1 = leftBranch m wd wallStar := by
  refine wd.tracks.iso.vtx.injective ?_
  have h : graph.vert (wd.tracks.iso.dart (coverDart m wd z)) =
      wd.tracks.iso.vtx (coverDart m wd z).1 := wd.tracks.iso.vert_map (coverDart m wd z)
  rw [dart_coverDart] at h
  rw [← h, hz]
  exact vert_base_eq m wd wallStar hBase

include wallStar in
theorem coverDart_vertex_right (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (z : D) (hz : graph.vert z = graph.vert (graph.op m.base)) :
    (coverDart m wd z).1 = rightBranch m wd wallStar := by
  refine wd.tracks.iso.vtx.injective ?_
  have h : graph.vert (wd.tracks.iso.dart (coverDart m wd z)) =
      wd.tracks.iso.vtx (coverDart m wd z).1 := wd.tracks.iso.vert_map (coverDart m wd z)
  rw [dart_coverDart] at h
  rw [← h, hz]
  exact vert_opBase_eq m wd wallStar hBase

/-- The wall row of the occurrence of a dart other than the two darts of the
contracted edge. -/
def endWallRow (z : D) (h₁ : z ≠ m.base) (h₂ : z ≠ graph.op m.base) :
    StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  (exists_inRow m wd (coverDart m wd z).2.1.stablePath (row_ne_facetRow m wd z h₁ h₂)).choose

theorem inRow_endWallRow (z : D) (h₁ : z ≠ m.base) (h₂ : z ≠ graph.op m.base) :
    inRow m wd (endWallRow m wd z h₁ h₂) = (coverDart m wd z).2.1.stablePath :=
  (exists_inRow m wd (coverDart m wd z).2.1.stablePath (row_ne_facetRow m wd z h₁ h₂)).choose_spec

/-! ## 4.  The star of each end, split over its two non-vanishing darts -/

section Ends

variable (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)

include wallStar hBase in
theorem incidentEdges_leftEnd :
    incidentEdges wd.cover (leftEnd m wd) =
      {facetEdge m wd, (coverDart m wd (thirdLeft m)).2.1, (coverDart m wd m.left).2.1} := by
  classical
  have h3 : nonDanglingValency wd.cover (leftEnd m wd) = 3 := by
    have h1 := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_leftEnd m wd)
    have h2 : nonDanglingValency wd.cover (leftEnd m wd) ≤ 3 := wd.fullDim.trivalent (leftEnd m wd)
    omega
  have hvt : (coverDart m wd (thirdLeft m)).1 = leftBranch m wd wallStar :=
    coverDart_vertex_left m wd wallStar hBase _ (thirdLeft_vert m)
  have hvl : (coverDart m wd m.left).1 = leftBranch m wd wallStar :=
    coverDart_vertex_left m wd wallStar hBase _ m.left_vert
  have hft : (coverDart m wd (thirdLeft m)).2.1 ≠ facetEdge m wd :=
    coverDart_ne_facetEdge m wd _ (thirdLeft_ne_base m) (thirdLeft_ne_opBase m)
  have hfl : (coverDart m wd m.left).2.1 ≠ facetEdge m wd :=
    coverDart_ne_facetEdge m wd _ m.left_ne (Ne.symm m.opBase_ne_left)
  have htl : (coverDart m wd (thirdLeft m)).2.1 ≠ (coverDart m wd m.left).2.1 := by
    intro hBad
    have hEq := dart_ext m wd (hvt.trans hvl.symm) hBad
    refine thirdLeft_ne_left m ?_
    have h := congrArg wd.tracks.iso.dart hEq
    rwa [dart_coverDart, dart_coverDart] at h
  have hv1 : (coverDart m wd (thirdLeft m)).1.1 = leftEnd m wd :=
    congrArg Subtype.val hvt
  have hv2 : (coverDart m wd m.left).1.1 = leftEnd m wd :=
    congrArg Subtype.val hvl
  have hincT : Incident wd.cover (coverDart m wd (thirdLeft m)).2.1.1 (leftEnd m wd) := by
    rw [← hv1]
    exact (coverDart m wd (thirdLeft m)).2.2
  have hincL : Incident wd.cover (coverDart m wd m.left).2.1.1 (leftEnd m wd) := by
    rw [← hv2]
    exact (coverDart m wd m.left).2.2
  have hsub : ({facetEdge m wd, (coverDart m wd (thirdLeft m)).2.1,
      (coverDart m wd m.left).2.1} : Finset (NonDanglingEdge wd.cover)) ⊆
      incidentEdges wd.cover (leftEnd m wd) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rw [mem_incidentEdges]
    rcases he with rfl | rfl | rfl
    · exact incident_facetEdge_leftEnd m wd
    · exact hincT
    · exact hincL
  have hcard : ({facetEdge m wd, (coverDart m wd (thirdLeft m)).2.1,
      (coverDart m wd m.left).2.1} : Finset (NonDanglingEdge wd.cover)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨fun h ↦ hft h.symm, fun h ↦ hfl h.symm⟩),
      Finset.card_insert_of_notMem (by simpa using htl), Finset.card_singleton]
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, card_incidentEdges, h3]

include wallStar hBase in
theorem incidentEdges_rightEnd :
    incidentEdges wd.cover (rightEnd m wd) =
      {facetEdge m wd, (coverDart m wd m.right).2.1, (coverDart m wd (thirdRight m)).2.1} := by
  classical
  have h3 : nonDanglingValency wd.cover (rightEnd m wd) = 3 := by
    have h1 := three_le_nonDanglingValency_end m wd wallStar _ (incident_facetEdge_rightEnd m wd)
    have h2 : nonDanglingValency wd.cover (rightEnd m wd) ≤ 3 :=
      wd.fullDim.trivalent (rightEnd m wd)
    omega
  have hvt : (coverDart m wd m.right).1 = rightBranch m wd wallStar :=
    coverDart_vertex_right m wd wallStar hBase _ m.right_vert
  have hvl : (coverDart m wd (thirdRight m)).1 = rightBranch m wd wallStar :=
    coverDart_vertex_right m wd wallStar hBase _ (thirdRight_vert m)
  have hft : (coverDart m wd m.right).2.1 ≠ facetEdge m wd :=
    coverDart_ne_facetEdge m wd _ (Ne.symm m.base_ne_right) m.right_ne
  have hfl : (coverDart m wd (thirdRight m)).2.1 ≠ facetEdge m wd :=
    coverDart_ne_facetEdge m wd _ (thirdRight_ne_base m) (thirdRight_ne_opBase m)
  have htl : (coverDart m wd m.right).2.1 ≠ (coverDart m wd (thirdRight m)).2.1 := by
    intro hBad
    have hEq := dart_ext m wd (hvt.trans hvl.symm) hBad
    refine right_ne_thirdRight m ?_
    have h := congrArg wd.tracks.iso.dart hEq
    rwa [dart_coverDart, dart_coverDart] at h
  have hv1 : (coverDart m wd m.right).1.1 = rightEnd m wd :=
    congrArg Subtype.val hvt
  have hv2 : (coverDart m wd (thirdRight m)).1.1 = rightEnd m wd :=
    congrArg Subtype.val hvl
  have hincT : Incident wd.cover (coverDart m wd m.right).2.1.1 (rightEnd m wd) := by
    rw [← hv1]
    exact (coverDart m wd m.right).2.2
  have hincL : Incident wd.cover (coverDart m wd (thirdRight m)).2.1.1 (rightEnd m wd) := by
    rw [← hv2]
    exact (coverDart m wd (thirdRight m)).2.2
  have hsub : ({facetEdge m wd, (coverDart m wd m.right).2.1,
      (coverDart m wd (thirdRight m)).2.1} : Finset (NonDanglingEdge wd.cover)) ⊆
      incidentEdges wd.cover (rightEnd m wd) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rw [mem_incidentEdges]
    rcases he with rfl | rfl | rfl
    · exact incident_facetEdge_rightEnd m wd
    · exact hincT
    · exact hincL
  have hcard : ({facetEdge m wd, (coverDart m wd m.right).2.1,
      (coverDart m wd (thirdRight m)).2.1} : Finset (NonDanglingEdge wd.cover)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨fun h ↦ hft h.symm, fun h ↦ hfl h.symm⟩),
      Finset.card_insert_of_notMem (by simpa using htl), Finset.card_singleton]
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, card_incidentEdges, h3]

include wallStar hBase in
theorem incidenceCount_leftEnd (ρ : StablePath wd.cover) (hρ : ρ ≠ facetRow m wd) :
    incidenceCount wd.cover (leftEnd m wd) ρ =
      (if (coverDart m wd (thirdLeft m)).2.1.stablePath = ρ then 1 else 0) +
        (if (coverDart m wd m.left).2.1.stablePath = ρ then 1 else 0) := by
  classical
  have hft : (coverDart m wd (thirdLeft m)).2.1 ≠ facetEdge m wd :=
    coverDart_ne_facetEdge m wd _ (thirdLeft_ne_base m) (thirdLeft_ne_opBase m)
  have hfl : (coverDart m wd m.left).2.1 ≠ facetEdge m wd :=
    coverDart_ne_facetEdge m wd _ m.left_ne (Ne.symm m.opBase_ne_left)
  have hvt : (coverDart m wd (thirdLeft m)).1 = leftBranch m wd wallStar :=
    coverDart_vertex_left m wd wallStar hBase _ (thirdLeft_vert m)
  have hvl : (coverDart m wd m.left).1 = leftBranch m wd wallStar :=
    coverDart_vertex_left m wd wallStar hBase _ m.left_vert
  have htl : (coverDart m wd (thirdLeft m)).2.1 ≠ (coverDart m wd m.left).2.1 := by
    intro hBad
    have hEq := dart_ext m wd (hvt.trans hvl.symm) hBad
    refine thirdLeft_ne_left m ?_
    have h := congrArg wd.tracks.iso.dart hEq
    rwa [dart_coverDart, dart_coverDart] at h
  rw [incidenceCount, incidentEdges_leftEnd m wd wallStar hBase, Finset.card_filter,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨fun h ↦ hft h.symm, fun h ↦ hfl h.symm⟩),
    Finset.sum_insert (by simpa using htl), Finset.sum_singleton,
    if_neg (by rw [facetEdge_stablePath m wd]; exact fun h ↦ hρ h.symm)]
  ring

include wallStar hBase in
theorem incidenceCount_rightEnd (ρ : StablePath wd.cover) (hρ : ρ ≠ facetRow m wd) :
    incidenceCount wd.cover (rightEnd m wd) ρ =
      (if (coverDart m wd m.right).2.1.stablePath = ρ then 1 else 0) +
        (if (coverDart m wd (thirdRight m)).2.1.stablePath = ρ then 1 else 0) := by
  classical
  have hft : (coverDart m wd m.right).2.1 ≠ facetEdge m wd :=
    coverDart_ne_facetEdge m wd _ (Ne.symm m.base_ne_right) m.right_ne
  have hfl : (coverDart m wd (thirdRight m)).2.1 ≠ facetEdge m wd :=
    coverDart_ne_facetEdge m wd _ (thirdRight_ne_base m) (thirdRight_ne_opBase m)
  have hvt : (coverDart m wd m.right).1 = rightBranch m wd wallStar :=
    coverDart_vertex_right m wd wallStar hBase _ m.right_vert
  have hvl : (coverDart m wd (thirdRight m)).1 = rightBranch m wd wallStar :=
    coverDart_vertex_right m wd wallStar hBase _ (thirdRight_vert m)
  have htl : (coverDart m wd m.right).2.1 ≠ (coverDart m wd (thirdRight m)).2.1 := by
    intro hBad
    have hEq := dart_ext m wd (hvt.trans hvl.symm) hBad
    refine right_ne_thirdRight m ?_
    have h := congrArg wd.tracks.iso.dart hEq
    rwa [dart_coverDart, dart_coverDart] at h
  rw [incidenceCount, incidentEdges_rightEnd m wd wallStar hBase, Finset.card_filter,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨fun h ↦ hft h.symm, fun h ↦ hfl h.symm⟩),
    Finset.sum_insert (by simpa using htl), Finset.sum_singleton,
    if_neg (by rw [facetEdge_stablePath m wd]; exact fun h ↦ hρ h.symm)]
  ring

end Ends

/-! ## 5.  The four rows at the ends, and the census -/

section Rows

/-- The wall row of the dart the move **keeps** at `graph.vert m.base`. -/
def keptRow : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  endWallRow m wd (thirdLeft m) (thirdLeft_ne_base m) (thirdLeft_ne_opBase m)

/-- The wall row of the dart the move **sends away** from `graph.vert m.base`. -/
def sentRow : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  endWallRow m wd m.left m.left_ne (Ne.symm m.opBase_ne_left)

/-- The wall row of the dart the move **brings over** to `graph.vert m.base`. -/
def broughtRow : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  endWallRow m wd m.right (Ne.symm m.base_ne_right) m.right_ne

/-- The wall row of the dart that **stays** at the other end. -/
def stayedRow : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  endWallRow m wd (thirdRight m) (thirdRight_ne_base m) (thirdRight_ne_opBase m)

theorem inRow_keptRow :
    inRow m wd (keptRow m wd) = (coverDart m wd (thirdLeft m)).2.1.stablePath :=
  inRow_endWallRow m wd _ _ _

theorem inRow_sentRow : inRow m wd (sentRow m wd) = (coverDart m wd m.left).2.1.stablePath :=
  inRow_endWallRow m wd _ _ _

theorem inRow_broughtRow :
    inRow m wd (broughtRow m wd) = (coverDart m wd m.right).2.1.stablePath :=
  inRow_endWallRow m wd _ _ _

theorem inRow_stayedRow :
    inRow m wd (stayedRow m wd) = (coverDart m wd (thirdRight m)).2.1.stablePath :=
  inRow_endWallRow m wd _ _ _

include wallStar in
/-- **The mirror move keeps the dart `m` sends away.** -/
theorem keptRow_mirror : keptRow (mirror m) wd = sentRow m wd := by
  refine inRow_injective m wd wallStar ?_
  have h1 : inRow m wd (keptRow (mirror m) wd) =
      (coverDart m wd (thirdLeft (mirror m))).2.1.stablePath := inRow_keptRow (mirror m) wd
  rw [h1, thirdLeft_mirror m, inRow_sentRow m wd]

include wallStar in
/-- **The mirror move brings over the dart that stays put under `m`.** -/
theorem broughtRow_mirror : broughtRow (mirror m) wd = stayedRow m wd := by
  refine inRow_injective m wd wallStar ?_
  have h1 : inRow m wd (broughtRow (mirror m) wd) =
      (coverDart m wd (thirdRight m)).2.1.stablePath := inRow_broughtRow (mirror m) wd
  rw [h1, inRow_stayedRow m wd]

include wallStar src hValid in
/-- **The row census at a three-valent wall.**  The four rows the two
complementary moves read off the two ends of the vanishing occurrence are, with
multiplicity, the four rows of the anchor survivors. -/
theorem census (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)
    (r : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    (if (doubledND src false).stablePath = r then 1 else 0) +
        (if (doubledND src true).stablePath = r then 1 else 0) +
        (if (simpleND src false).stablePath = r then 1 else 0) +
        (if (simpleND src true).stablePath = r then 1 else 0) =
      (if keptRow m wd = r then 1 else 0) + (if sentRow m wd = r then 1 else 0) +
        (if broughtRow m wd = r then 1 else 0) + (if stayedRow m wd = r then 1 else 0) := by
  classical
  have hconv : ∀ (z : D) (w : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)),
      inRow m wd w = (coverDart m wd z).2.1.stablePath →
      (if (coverDart m wd z).2.1.stablePath = inRow m wd r then 1 else 0) =
        (if w = r then 1 else 0) := by
    intro z w hw
    have hiff : ((coverDart m wd z).2.1.stablePath = inRow m wd r) ↔ (w = r) := by
      rw [← hw]
      exact ⟨fun h ↦ inRow_injective m wd wallStar h, fun h ↦ congrArg _ h⟩
    by_cases hc : w = r
    · rw [if_pos (hiff.mpr hc), if_pos hc]
    · rw [if_neg (fun hbad ↦ hc (hiff.mp hbad)), if_neg hc]
  have h4 : incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (anchorVertex m wd anchorBlk) r =
        (if (doubledND src false).stablePath = r then 1 else 0) +
        (if (doubledND src true).stablePath = r then 1 else 0) +
        (if (simpleND src false).stablePath = r then 1 else 0) +
        (if (simpleND src true).stablePath = r then 1 else 0) := incidenceCount_anchor_four src r
  have h1 := incidenceCount_anchor_eq_ends m wd wallStar src hValid r
  have h2 := incidenceCount_leftEnd m wd wallStar hBase (inRow m wd r) (inRow_ne_facetRow m wd r)
  have h3 := incidenceCount_rightEnd m wd wallStar hBase (inRow m wd r) (inRow_ne_facetRow m wd r)
  rw [hconv (thirdLeft m) (keptRow m wd) (inRow_keptRow m wd),
    hconv m.left (sentRow m wd) (inRow_sentRow m wd)] at h2
  rw [hconv m.right (broughtRow m wd) (inRow_broughtRow m wd),
    hconv (thirdRight m) (stayedRow m wd) (inRow_stayedRow m wd)] at h3
  omega

/-- Two pairs with the same counting function are the same pair, in one of the
two orders. -/
private theorem pair_of_count_eq {α : Type*} [DecidableEq α] {a b c d : α}
    (h : ∀ r : α, (if a = r then 1 else 0) + (if b = r then 1 else 0)
      = (if c = r then 1 else 0) + (if d = r then 1 else 0)) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  classical
  have h1 := h a
  have h2 := h b
  have haa : (if a = a then (1 : ℕ) else 0) = 1 := if_pos rfl
  have hbb : (if b = b then (1 : ℕ) else 0) = 1 := if_pos rfl
  rw [haa] at h1
  rw [hbb] at h2
  by_cases hca : c = a
  · subst hca
    refine Or.inl ⟨rfl, ?_⟩
    by_cases hdb : d = b
    · exact hdb
    · rw [if_neg hdb] at h2
      omega
  · have hda : d = a := by
      by_cases hd : d = a
      · exact hd
      · rw [if_neg hca, if_neg hd] at h1
        omega
    subst hda
    refine Or.inr ⟨?_, rfl⟩
    by_cases hcb : c = b
    · exact hcb
    · rw [if_neg hcb] at h2
      omega

include wallStar src hValid in
/-- **The move-to-partition classification at a three-valent wall.**  The pair of
rows the move places at `graph.vert m.base` is the doubled pair, or the simple
pair, or one of each -- and in the last two cases the complementary pair, which
is what the mirror move places there, is the complementary pair of survivors. -/
theorem classify (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base) :
    (∃ j : Bool, keptRow m wd = (doubledND src j).stablePath ∧
        broughtRow m wd = (doubledND src (!j)).stablePath) ∨
      (∃ j : Bool, sentRow m wd = (doubledND src j).stablePath ∧
          stayedRow m wd = (doubledND src (!j)).stablePath) ∨
        (∃ i j : Bool,
          ((keptRow m wd = (simpleND src i).stablePath ∧
              broughtRow m wd = (doubledND src j).stablePath) ∨
            (keptRow m wd = (doubledND src j).stablePath ∧
              broughtRow m wd = (simpleND src i).stablePath)) ∧
          ((sentRow m wd = (doubledND src (!j)).stablePath ∧
              stayedRow m wd = (simpleND src (!i)).stablePath) ∨
            (sentRow m wd = (simpleND src (!i)).stablePath ∧
              stayedRow m wd = (doubledND src (!j)).stablePath))) := by
  classical
  have hc := census m wd wallStar src hValid hBase
  have hswapD : ∀ (b : Bool) (r : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)),
      (if (doubledND src false).stablePath = r then 1 else 0) +
          (if (doubledND src true).stablePath = r then 1 else 0) =
        (if (doubledND src b).stablePath = r then 1 else 0) +
          (if (doubledND src (!b)).stablePath = r then 1 else 0) := by
    intro b r
    cases b
    · simp only [Bool.not_false]
    · simp only [Bool.not_true]
      omega
  have hswapS : ∀ (b : Bool) (r : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)),
      (if (simpleND src false).stablePath = r then 1 else 0) +
          (if (simpleND src true).stablePath = r then 1 else 0) =
        (if (simpleND src b).stablePath = r then 1 else 0) +
          (if (simpleND src (!b)).stablePath = r then 1 else 0) := by
    intro b r
    cases b
    · simp only [Bool.not_false]
    · simp only [Bool.not_true]
      omega
  by_cases hkd : ∃ j : Bool, (doubledND src j).stablePath = keptRow m wd
  · obtain ⟨j, hj⟩ := hkd
    by_cases hbd : (doubledND src (!j)).stablePath = broughtRow m wd
    · exact Or.inl ⟨j, hj.symm, hbd.symm⟩
    · have hbs : ∃ i : Bool, (simpleND src i).stablePath = broughtRow m wd := by
        by_contra hno
        push Not at hno
        have hA := hc (broughtRow m wd)
        have hD := hswapD j (broughtRow m wd)
        have e1 : (if (doubledND src (!j)).stablePath = broughtRow m wd then 1 else 0) = 0 :=
          if_neg hbd
        have e2 : (if (simpleND src false).stablePath = broughtRow m wd then 1 else 0) = 0 :=
          if_neg (hno false)
        have e3 : (if (simpleND src true).stablePath = broughtRow m wd then 1 else 0) = 0 :=
          if_neg (hno true)
        have e4 : (if broughtRow m wd = broughtRow m wd then (1 : ℕ) else 0) = 1 := if_pos rfl
        have e5 : (if (doubledND src j).stablePath = broughtRow m wd then 1 else 0) =
            (if keptRow m wd = broughtRow m wd then 1 else 0) := by rw [hj]
        omega
      obtain ⟨i, hi⟩ := hbs
      have hcan : ∀ r : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
          (if (doubledND src (!j)).stablePath = r then 1 else 0) +
              (if (simpleND src (!i)).stablePath = r then 1 else 0) =
            (if sentRow m wd = r then 1 else 0) + (if stayedRow m wd = r then 1 else 0) := by
        intro r
        have hA := hc r
        have hD := hswapD j r
        have hS := hswapS i r
        have e1 : (if (doubledND src j).stablePath = r then 1 else 0) =
            (if keptRow m wd = r then 1 else 0) := by rw [hj]
        have e2 : (if (simpleND src i).stablePath = r then 1 else 0) =
            (if broughtRow m wd = r then 1 else 0) := by rw [hi]
        omega
      rcases pair_of_count_eq hcan with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inr ⟨i, j, Or.inr ⟨hj.symm, hi.symm⟩, Or.inl ⟨h1, h2⟩⟩)
      · exact Or.inr (Or.inr ⟨i, j, Or.inr ⟨hj.symm, hi.symm⟩, Or.inr ⟨h1, h2⟩⟩)
  · push Not at hkd
    have hks : ∃ i : Bool, (simpleND src i).stablePath = keptRow m wd := by
      by_contra hno
      push Not at hno
      have hA := hc (keptRow m wd)
      have e1 : (if (doubledND src false).stablePath = keptRow m wd then 1 else 0) = 0 :=
        if_neg (hkd false)
      have e2 : (if (doubledND src true).stablePath = keptRow m wd then 1 else 0) = 0 :=
        if_neg (hkd true)
      have e3 : (if (simpleND src false).stablePath = keptRow m wd then 1 else 0) = 0 :=
        if_neg (hno false)
      have e4 : (if (simpleND src true).stablePath = keptRow m wd then 1 else 0) = 0 :=
        if_neg (hno true)
      have e5 : (if keptRow m wd = keptRow m wd then (1 : ℕ) else 0) = 1 := if_pos rfl
      omega
    obtain ⟨i, hi⟩ := hks
    by_cases hbd : ∃ j : Bool, (doubledND src j).stablePath = broughtRow m wd
    · obtain ⟨j, hj⟩ := hbd
      have hcan : ∀ r : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
          (if (doubledND src (!j)).stablePath = r then 1 else 0) +
              (if (simpleND src (!i)).stablePath = r then 1 else 0) =
            (if sentRow m wd = r then 1 else 0) + (if stayedRow m wd = r then 1 else 0) := by
        intro r
        have hA := hc r
        have hD := hswapD j r
        have hS := hswapS i r
        have e1 : (if (doubledND src j).stablePath = r then 1 else 0) =
            (if broughtRow m wd = r then 1 else 0) := by rw [hj]
        have e2 : (if (simpleND src i).stablePath = r then 1 else 0) =
            (if keptRow m wd = r then 1 else 0) := by rw [hi]
        omega
      rcases pair_of_count_eq hcan with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inr ⟨i, j, Or.inl ⟨hi.symm, hj.symm⟩, Or.inl ⟨h1, h2⟩⟩)
      · exact Or.inr (Or.inr ⟨i, j, Or.inl ⟨hi.symm, hj.symm⟩, Or.inr ⟨h1, h2⟩⟩)
    · push Not at hbd
      have hbs : (simpleND src (!i)).stablePath = broughtRow m wd := by
        by_contra hno
        have hA := hc (broughtRow m wd)
        have hS := hswapS i (broughtRow m wd)
        have e1 : (if (doubledND src false).stablePath = broughtRow m wd then 1 else 0) = 0 :=
          if_neg (hbd false)
        have e2 : (if (doubledND src true).stablePath = broughtRow m wd then 1 else 0) = 0 :=
          if_neg (hbd true)
        have e3 : (if (simpleND src (!i)).stablePath = broughtRow m wd then 1 else 0) = 0 :=
          if_neg hno
        have e4 : (if broughtRow m wd = broughtRow m wd then (1 : ℕ) else 0) = 1 := if_pos rfl
        have e5 : (if (simpleND src i).stablePath = broughtRow m wd then 1 else 0) =
            (if keptRow m wd = broughtRow m wd then 1 else 0) := by rw [hi]
        omega
      have hcan : ∀ r : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
          (if (doubledND src false).stablePath = r then 1 else 0) +
              (if (doubledND src true).stablePath = r then 1 else 0) =
            (if sentRow m wd = r then 1 else 0) + (if stayedRow m wd = r then 1 else 0) := by
        intro r
        have hA := hc r
        have hS := hswapS i r
        have e1 : (if (simpleND src i).stablePath = r then 1 else 0) =
            (if keptRow m wd = r then 1 else 0) := by rw [hi]
        have e2 : (if (simpleND src (!i)).stablePath = r then 1 else 0) =
            (if broughtRow m wd = r then 1 else 0) := by rw [hbs]
        omega
      rcases pair_of_count_eq hcan with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨false, h1, h2⟩)
      · exact Or.inr (Or.inl ⟨true, h1, h2⟩)

end Rows

/-! ## 6.  The link, in each of the three cases -/

section Links

open NonTrivalentValencyThreeSimpleCandidate

/-- The Type I / Type II base with `alphaLabel = simpleLabel i` and the doubled
survivor `j` at `A_u`. -/
def simpleBaseOf (i j : Bool)
    (hR : directionIndex (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (simpleLabel src (!i)) +
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex (doubledSur src j).1 ≤
      ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
        ⟨wd.a, wd.hab⟩).blockCard anchorBlk.1) :
    SimpleBase (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk where
  source := src
  noGlue := hNoGlue
  connected := wd.wallTarget_connected
  genusZero := wd.wallTarget_genus
  alphaLabel := simpleLabel src i
  betaLabel := simpleLabel src (!i)
  alpha_ne := simpleLabel_ne_doubled src i
  beta_ne := simpleLabel_ne_doubled src (!i)
  beta_ne_alpha := (simpleLabel_ne_simpleLabel src i).symm
  swapDoubled := j
  realizable := hR

theorem doubledLift_eq (b : Bool) :
    doubledLift m wd src b = liftEdge m wd (doubledND src b) := by
  cases b <;> rfl

/-- The realisability inequality of `simpleBaseOf i j`. -/
def Realisable (i j : Bool) : Prop :=
  directionIndex (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
      (simpleLabel src (!i)) +
    (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex (doubledSur src j).1 ≤
    ((contractDatum wd.cover wd.hc wd.hab wd.hOne).vertexPartition
      ⟨wd.a, wd.hab⟩).blockCard anchorBlk.1

/-- **Exactly one of the two complementary realisations of a simple partition
exists**: the four survivor indices sum to `2|A| + 1`. -/
theorem realisable_or (i j : Bool) :
    Realisable m wd wallStar src i j ∨ Realisable m wd wallStar src (!i) (!j) := by
  have h := sum_index_four src i j
  cases i <;> cases j <;>
    simp only [Realisable, Bool.not_false, Bool.not_true] at h ⊢ <;> omega

theorem alphaLift_eq (i j : Bool) (hR : Realisable m wd wallStar src i j) :
    NonTrivalentValencyThreeSimpleTracks.alphaLift m wd
        (simpleBaseOf m wd wallStar src hNoGlue i j hR) =
      liftEdge m wd (simpleND src i) := rfl

theorem deltaLift_eq (i j : Bool) (hR : Realisable m wd wallStar src i j) :
    NonTrivalentValencyThreeSimpleTracks.deltaLift m wd
        (simpleBaseOf m wd wallStar src hNoGlue i j hR) =
      liftEdge m wd (doubledND src j) := rfl

variable (hBase : wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base)

include wd in
theorem movedStar_darts :
    (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {wd.tracks.iso.dart (coverDart m wd (thirdLeft m)),
        wd.tracks.iso.dart (coverDart m wd m.right)} := by
  rw [dart_coverDart, dart_coverDart]
  exact movedStar_eq_pair m

include wallStar src hValid hNoGlue hBase in
/-- **Type III**: the move puts the two doubled-direction survivors at
`graph.vert m.base`. -/
theorem link_of_doubled (j : Bool)
    (hk : keptRow m wd = (doubledND src j).stablePath)
    (hb : broughtRow m wd = (doubledND src (!j)).stablePath) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  have hlift : ∀ b : Bool, (doubledLift m wd src b).stablePath =
      inRow m wd ((doubledND src b).stablePath) := by
    intro b
    rw [doubledLift_eq m wd wallStar src b]
    exact stablePath_liftEdge' m wd (doubledND src b)
  have hStar := movedStar_darts m wd
  have hkr : inRow m wd (keptRow m wd) = (coverDart m wd (thirdLeft m)).2.1.stablePath :=
    inRow_keptRow m wd
  have hbr : inRow m wd (broughtRow m wd) = (coverDart m wd m.right).2.1.stablePath :=
    inRow_broughtRow m wd
  cases j
  · simp only [Bool.not_false] at hb
    refine ⟨NonTrivalentValencyThreeStarCount.typeChangeLink_of_prescribedDoubledMove m wd
      wallStar src hNoGlue hValid
      (NonTrivalentValencyThreeTracks.prescribedDoubledMove_of_rows m wd wallStar src hBase
        (coverDart m wd (thirdLeft m)) (coverDart m wd m.right) ?_ ?_ hStar)⟩
    · rw [← hkr, hk, hlift false]
    · rw [← hbr, hb, hlift true]
  · simp only [Bool.not_true] at hb
    refine ⟨NonTrivalentValencyThreeStarCount.typeChangeLink_of_prescribedDoubledMove m wd
      wallStar src hNoGlue hValid
      (NonTrivalentValencyThreeTracks.prescribedDoubledMove_of_rows m wd wallStar src hBase
        (coverDart m wd m.right) (coverDart m wd (thirdLeft m)) ?_ ?_ ?_)⟩
    · rw [← hbr, hb, hlift false]
    · rw [← hkr, hk, hlift true]
    · rw [hStar, Finset.pair_comm]

include wallStar src hValid hNoGlue hBase in
/-- **Types I and II**: the move puts one simple and one doubled survivor at
`graph.vert m.base`, and that pair is the realisable one. -/
theorem link_of_simple (i j : Bool) (hR : Realisable m wd wallStar src i j)
    (hpair : (keptRow m wd = (simpleND src i).stablePath ∧
        broughtRow m wd = (doubledND src j).stablePath) ∨
      (keptRow m wd = (doubledND src j).stablePath ∧
        broughtRow m wd = (simpleND src i).stablePath)) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  have hStar := movedStar_darts m wd
  have halpha : (NonTrivalentValencyThreeSimpleTracks.alphaLift m wd
      (simpleBaseOf m wd wallStar src hNoGlue i j hR)).stablePath =
      inRow m wd ((simpleND src i).stablePath) := by
    rw [alphaLift_eq m wd wallStar src hNoGlue i j hR]
    exact stablePath_liftEdge' m wd (simpleND src i)
  have hdelta : (NonTrivalentValencyThreeSimpleTracks.deltaLift m wd
      (simpleBaseOf m wd wallStar src hNoGlue i j hR)).stablePath =
      inRow m wd ((doubledND src j).stablePath) := by
    rw [deltaLift_eq m wd wallStar src hNoGlue i j hR]
    exact stablePath_liftEdge' m wd (doubledND src j)
  rcases hpair with ⟨hk, hb⟩ | ⟨hk, hb⟩
  · refine ⟨NonTrivalentValencyThreeSimpleStarCount.typeChangeLink_of_prescribedSimpleMove m wd
      (simpleBaseOf m wd wallStar src hNoGlue i j hR) hValid
      (NonTrivalentValencyThreeSimpleTracks.prescribedSimpleMove_of_rows m wd
        (simpleBaseOf m wd wallStar src hNoGlue i j hR) hBase
        (coverDart m wd (thirdLeft m)) (coverDart m wd m.right) ?_ ?_ hStar)⟩
    · rw [halpha, ← hk]
      exact (inRow_keptRow m wd).symm
    · rw [hdelta, ← hb]
      exact (inRow_broughtRow m wd).symm
  · refine ⟨NonTrivalentValencyThreeSimpleStarCount.typeChangeLink_of_prescribedSimpleMove m wd
      (simpleBaseOf m wd wallStar src hNoGlue i j hR) hValid
      (NonTrivalentValencyThreeSimpleTracks.prescribedSimpleMove_of_rows m wd
        (simpleBaseOf m wd wallStar src hNoGlue i j hR) hBase
        (coverDart m wd m.right) (coverDart m wd (thirdLeft m)) ?_ ?_ ?_)⟩
    · rw [halpha, ← hb]
      exact (inRow_broughtRow m wd).symm
    · rw [hdelta, ← hk]
      exact (inRow_keptRow m wd).symm
    · rw [hStar, Finset.pair_comm]

include wallStar src hValid hNoGlue hBase in
/-- **The link at a three-valent wall whose vanishing occurrence is oriented
with its `A_u` end at `graph.vert m.base`.**  The move puts one row from each
end of the vanishing occurrence at `graph.vert m.base`; the census identifies
that pair with a pair of anchor survivors, and the mirror move supplies the
complementary pair whenever the pair the move names is not the one the
constructed candidate of that partition realises. -/
theorem nonempty_typeChangeLink_of_orientation : Nonempty (TypeChangeLink m wd) := by
  classical
  have hL : label (graph.op m.base) = label m.base :=
    MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
  have hBase' : wd.tracks.iso.dart (facetDartLeft (mirror m) wd wallStar) = (mirror m).base := hBase
  rcases classify m wd wallStar src hValid hBase with hA | hB | hC
  · obtain ⟨j, hk, hb⟩ := hA
    exact link_of_doubled m wd wallStar src hValid hNoGlue hBase j hk hb
  · obtain ⟨j, hs, hst⟩ := hB
    refine MoveMirror.nonempty_typeChangeLink_of_mirror m wd hL ?_
    refine link_of_doubled (mirror m) wd wallStar src hValid hNoGlue hBase' j ?_ ?_
    · rw [keptRow_mirror m wd wallStar]
      exact hs
    · rw [broughtRow_mirror m wd wallStar]
      exact hst
  · obtain ⟨i, j, hp, hq⟩ := hC
    rcases realisable_or m wd wallStar src i j with hR | hR
    · exact link_of_simple m wd wallStar src hValid hNoGlue hBase i j hR hp
    · refine MoveMirror.nonempty_typeChangeLink_of_mirror m wd hL ?_
      refine link_of_simple (mirror m) wd wallStar src hValid hNoGlue hBase' (!i) (!j) hR ?_
      rw [keptRow_mirror m wd wallStar, broughtRow_mirror m wd wallStar]
      exact hq.symm

end Links

end Census

/-! ## 7.  The orientation normalisation, and the headline -/

section Headline

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

include wd in
/-- **The orientation dichotomy at a three-valent wall.** -/
theorem dart_facetDartLeft_cases_three
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    wd.tracks.iso.dart (facetDartLeft m wd wallStar) = m.base ∨
      wd.tracks.iso.dart (facetDartLeft m wd wallStar) = graph.op m.base := by
  classical
  have hLab : label (wd.tracks.iso.dart (facetDartLeft m wd wallStar)) = label m.base := by
    rw [wd.tracks.row_map (facetDartLeft m wd wallStar)]
    show wd.fullDim.labelling.row (facetEdge m wd).stablePath = label m.base
    rw [facetEdge_stablePath m wd]
    exact Equiv.apply_symm_apply _ _
  have hmem : wd.tracks.iso.dart (facetDartLeft m wd wallStar) ∈
      (Finset.univ.filter fun d : D ↦ label d = label m.base) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLab⟩
  rw [NonTrivalentValencyFourDispatcher.filter_label_base m wd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem

variable (hL : label (graph.op m.base) = label m.base)

/-- The vanishing row is unchanged when the move is read from the other end. -/
theorem facetRow_swap_three :
    facetRow m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) = facetRow m wd := by
  show wd.fullDim.labelling.row.symm (label (graph.op m.base)) = _
  rw [hL]
  rfl

/-- Hence so is the vanishing occurrence (`eq_facetEdge` at valency three). -/
theorem facetEdge_swap_three
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    facetEdge m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) = facetEdge m wd :=
  eq_facetEdge m wd wallStar
    (facetEdge m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL))
    ((facetEdge_stablePath m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL)).trans
      (facetRow_swap_three m wd hL))

/-- Hence so is its dart at the `A_u` end. -/
theorem facetDartLeft_swap_three
    (wallStar : ThreeStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    facetDartLeft m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) wallStar =
      facetDartLeft m wd wallStar :=
  NonTrivalentValencyFourDispatcher.dartOfLeftEnd_congr wd.cover
    (facetEdge_swap_three m wd hL wallStar) _ _

/-- **`OuterWalk.TypeChangeLink` at every three-valent wall datum of every
Whitehead move, from the wall valency alone.** -/
theorem typeChangeLink_three
    (h3 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 3) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  obtain ⟨anchorBlk, src, hNoGlue, hValid, -, -⟩ :=
    NonTrivalentValencyThreeExit.exists_anchor_of_wallData m wd (ThreeStar.of_card h3)
  rcases dart_facetDartLeft_cases_three m wd (ThreeStar.of_card h3) with h | h
  · exact nonempty_typeChangeLink_of_orientation m wd (ThreeStar.of_card h3) src hValid hNoGlue h
  · have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    have hBase' : (NonTrivalentValencyFourDispatcher.swapWallData m wd hL).tracks.iso.dart
        (facetDartLeft m.swap (NonTrivalentValencyFourDispatcher.swapWallData m wd hL)
          (ThreeStar.of_card h3)) = m.swap.base :=
      (congrArg wd.tracks.iso.dart
        (facetDartLeft_swap_three m wd hL (ThreeStar.of_card h3))).trans h
    exact (nonempty_typeChangeLink_of_orientation m.swap
      (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) (ThreeStar.of_card h3) src hValid
      hNoGlue hBase').map (NonTrivalentValencyFourDispatcher.linkOfSwap m wd hL)

/-- The same headline in the shape the `link` binder asks for. -/
def typeChangeLink_three'
    (h3 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 3) :
    TypeChangeLink m wd :=
  (typeChangeLink_three m wd h3).some

/-- **The valency dispatcher at one wall**, with the four-valent branch
(`NonTrivalentValencyFourDispatcher`) and the three-valent branch discharged. -/
def typeChangeLink_of_valency_two
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩).card = 2 → TypeChangeLink m wd) :
    TypeChangeLink m wd := by
  classical
  by_cases h4 : (GluingDatum.incidentEdges
      (target := contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩).card = 4
  · exact NonTrivalentValencyFourDispatcher.typeChangeLink_four' m wd h4
  · by_cases h3 : (GluingDatum.incidentEdges
        (target := contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩).card = 3
    · exact typeChangeLink_three' m wd h3
    · refine h2 ?_
      rcases NonTrivalentValencyFourDispatcher.valency_four_or_three_or_two m wd with h | h | h
      · exact absurd h h4
      · exact absurd h h3
      · exact h

end Headline

/-! ## 8.  The `link` binder of the outer walk, with only valency two left -/

section Dispatch

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {label : D → coordinate}

/-- **The `link` binder of `OuterWalk.coneEntry_of_reaches`, with the four-valent
and three-valent branches discharged.**  Its remaining explicit parameter is the
valency-two exit, which `NonTrivalentValencyTwoBaseOneLink.link_all` discharges
unconditionally. -/
def link_of_valency_two {G : CubicDartGraph D V}
    (h2 : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival),
        (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 2 → TypeChangeLink m wd) :
    ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival), TypeChangeLink m wd :=
  fun K hK m arrival wd ↦ typeChangeLink_of_valency_two m wd (h2 K hK m arrival wd)

end Dispatch

end

end DraismaVargas.LocalCases.NonTrivalentValencyThreeDispatcher
