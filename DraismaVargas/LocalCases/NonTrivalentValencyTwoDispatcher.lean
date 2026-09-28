import DraismaVargas.LocalCases.NonTrivalentValencyFourDispatcher
import DraismaVargas.LocalCases.NonTrivalentValencyTwoStarCountAll
import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneTracks

/-!
# The valency-two move-to-family dispatcher: merges closed, cross pairs isolated

Source: Vargas, Part II, arXiv:2609.09109, Section 5.1 (the labelling convention at a
non-trivalent wall: the contracting edge `h_1` of the incoming type has two ends
`A_1`, `A_2`, and the four edges of `H_0` at the anchor `A` are distributed over
them) and Section 5.4 (case `{v2-nd4}`: the four survivors split `2 + 2` over the
two target directions -- Configuration A -- or `3 + 1` -- Configuration B; the
merge member of the base tree `T_2` exists in every sub-case, the Base I member
needs the two index equalities stated at the opening of Section 5.4, and the
split members need the strict index inequalities of the subcases
`{v2-nd4-t3-k2=k3}` and `{v2-nd4-t3-k2<k3}`; the closing count of the
valency-two analysis says that exactly one of Base I and split realises each
cross pairing), together with Draisma–Vargas Part I, arXiv:1909.12924 (the stable graph `H(M)`
and its row labels, and Case `{w2-r2}`, Base I).

`NonTrivalentValencyFourDispatcher.typeChangeLink_four` treats valency four,
leaving the walk's `link` binder with the valency-three and valency-two exits.
`NonTrivalentValencyTwoStarCountAll` turns the row-level (H-II)
`PrescribedMergedMoveAny` into `OuterWalk.TypeChangeLink` at **any** two-valent
Base II wall, `NonTrivalentValencyTwoBaseOneTracks` and
`NonTrivalentValencyTwoBaseOneStarCount` turn the row-level (H-BaseI) into the
link at a Configuration A Base I wall, and `NonTrivalentValencyTwoSplitExit`
supplies the Configuration A split exit.  This module discharges the Base II
half from the move itself and reduces everything that is left to a single,
explicitly named cross-pair hypothesis.

## What is proved

### 1--2.  The row census at the two anchor ends

`incidenceCount_anchor_eq_ends` is the main new statement of this module:

> for every stable row of the wall datum, the number of surviving occurrences at the
> anchor carrying it equals the number of occurrences of its incoming row at the `A_u`
> end plus the number at the `A_v` end.

`WallSplitIncidence.incidenceCount_anchor` proves this under the hypothesis that the
anchor fibre *is* the two ends, which fails at every incoming configuration with a
pass-through survivor (the split incomings of Configuration A and every
Configuration B incoming put a divalent vertex over the contracted edge inside the
fibre).  The proof here needs no such hypothesis, because it never looks inside the
fibre: a stable row meets its branch vertices twice in all, both upstairs and downstairs
(`NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex`, with
`HasPathEnds` of the wall datum supplied by `hasPathEnds_wall` at every two-valent wall);
away from the anchor the star of a row is unchanged (the (T2) statement
`NonTrivalentValencyTwoStarCountAll.incidenceCount_wall_eq_incoming`) and the branch
vertices correspond (`NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement`);
subtracting the two identities leaves exactly the claim.  A divalent pass-through
vertex is not a branch vertex on either side, so it never enters.

`sum_split_ends`, `incidenceCount_ends_le`, `anchorEnds_base` (the two ends the move
names *are* the two anchor ends, in that order),
`incidenceCount_ends_eq_zero_of_not_incomingRow` (a row that is not an incoming row meets
neither end -- both sides of the census add up to `nd(A) = 4`).

### 3--5.  The four darts the move sorts

`thirdBase`, `thirdOp`, `movedStar_base`, `movedStar_op`: the moved star of
`graph.vert m.base` with `m.base` removed is `{thirdBase, m.right}`, and the moved star
at the other end is the **complementary** pair `{thirdOp, m.left}` -- so the two
descriptions `m` and `m.swap` of the same Whitehead move name the two complementary
pairs of the four non-vanishing darts at the two ends.  In particular no move can name
the incoming pairing itself: its pair always straddles the two ends.  `move_ne`: no
Whitehead move is trivial either -- `graph.move m` is never `graph` -- so the dispatcher
never has to supply a link for a move that does not change the ambient graph.

`incidentEdges_baseEnd`, `incidentEdges_opEnd`, `incidenceCount_baseEnd_eq`,
`incidenceCount_opEnd_eq`, `rows_ne_facetRow`: each end is trivalent and carries exactly
one occurrence of the vanishing row, so the other two occurrences at each end carry four
rows `rowL`, `rowT`, `rowR`, `rowS`, none of them the vanishing row.

### 6--7.  The census as a matching

`card_filter_anchor_eq`: the census fibre by fibre.  `survEquiv`: the row-preserving
**bijection** `Fin 4 ≃ {surviving occurrences at the anchor}` it produces, with
`survRow_survEquiv` its defining property.  `card_thickPos_eq`,
`two_le_card_thickPos`: through the bijection the positions whose survivor lies over the
thick target direction are as many as the thick survivors, and there are at least two of
them in both distributions.  `thick_trichotomy`: either the move's own pair
(positions `1`, `2`) is a same-direction pair, or the complementary pair
(positions `3`, `0`) is, or the move's own pair is a cross pair and so is the
complementary one.

### 8--10.  The dispatch

* `nonempty_typeChangeLink_of_thick_rows`, `typeChangeLink_two_of_thick_pair`: **the
  merge**.  From two distinct survivors over the thick direction carrying the rows of
  the move's pair, (H-II) `PrescribedMergedMoveAny` is discharged by
  `movedStar_base`, and the headline of `NonTrivalentValencyTwoStarCountAll` gives
  the link.  No further hypothesis.
* `link_or_crossPair`: **the dispatch**.  At every two-valent wall datum either the link
  is already there -- by the merge for `m`, or for `m.swap` when the move's pair lies
  over the thin direction, transported by
  `NonTrivalentValencyFourDispatcher.linkOfSwap` -- or the wall carries the
  Configuration A `2 + 2` distribution and the move names a cross pair whose two members'
  incoming rows are the two rows the move names, in one of the two orders.
* `typeChangeLink_two`, `typeChangeLink_of_valency_two`: the link from the wall valency
  and the cross-pair hypothesis `CrossPairLink`.
* `typeChangeLink_two_of_three_thick`: **at a `3 + 1` wall every move is closed** with no
  hypothesis beyond the distribution -- three survivors over the thick direction leave at
  most one thin position, so `not_cross_of_three_thick` rules the cross case out.
* `BaseOneCrossLink`, `SplitCrossLink`, `crossPairLink_of_index_dichotomy`: (H-cross)
  splits into the Base I half (equal dilation indices, the index equalities of Part II,
  Section 5.4) and the split half (unequal indices, the subcases with strict index
  inequalities), which is how Part II's closing count of the valency-two analysis
  presents it.
* `crossPairLink_of_three_thick`, `crossPairLink_of_link`,
  `baseOneCrossLink_of_three_thick`, `splitCrossLink_of_three_thick`: relative
  non-vacuity of the three hypotheses.
* `link_of_valency_three`, `link_of_valency_three_of_dichotomy`: the `link` binder of
  `OuterWalk.coneEntry_of_reaches` with the four-valent branch
  (`NonTrivalentValencyFourDispatcher`) and the two-valent branch discharged, leaving
  the valency-three exit and (H-cross), the latter in one piece or split into its two
  families.

## The hypotheses of this module, and where they are discharged

The theorems below take the following as explicit hypotheses; all three are
discharged elsewhere, closing the walk's `link` binder with no hypothesis
(`NonTrivalentValencyTwoBaseOneLink.link_all`).

1. `CrossPairLink m wd h2`, i.e. (H-cross): at a `2 + 2` Configuration A wall, a
   prescribed **cross** pairing is realised.  Everything else at valency two is
   discharged here: the anchor block, the two-branch anchor, the ordinary-block
   trivalence, the wall labelling of `NonTrivalentValencyTwoExitFree`, the anchor ends,
   the incoming `2 + 2` / `1 + 3` / `3 + 1` trichotomy and (H-II) itself.
   `NonTrivalentValencyTwoBaseOneLink.crossPairLink` discharges (H-cross)
   unconditionally, combining `baseOneCrossLink` and `splitCrossLink` via
   `crossPairLink_of_index_dichotomy` below.
2. The Base I half of (H-cross) needs one identification.  `BaseOneSetup` is a `Prop`,
   so `NonTrivalentValencyTwoBaseOne.BaseOneSetup.firstOf 0` -- and hence the cross
   pair `crossThick`/`crossThin` at `A_1` that (H-BaseI) names -- is a classical
   choice, and one must know whether it is the pair the move names or the
   complementary one.  Both cases are covered once that is known (the complementary
   one by `m.swap`, whose pair is exactly the complementary pair, `movedStar_op`).
   `NonTrivalentValencyTwoBaseOneLink.crossPair_identification` supplies that
   identification, from a variant of `exists_gauged_candidate_of_contraction` that
   keeps the pair conjuncts, giving `baseOneCrossLink`; the split half is
   `splitCrossLink`, from the split link of `NonTrivalentValencyTwoSplitStarCount`.
3. The valency-three branch of the `link` binder:
   `NonTrivalentValencyThreeDispatcher` discharges it with no hypothesis beyond the
   wall's own valency.

`IsThickSurv`, `CrossPairLink`, `BaseOneCrossLink` and `SplitCrossLink` are the `Prop`
definitions introduced; the first is an abbreviation used throughout, and the other three
come with `crossPairLink_of_three_thick`, `crossPairLink_of_link`,
`baseOneCrossLink_of_three_thick` and `splitCrossLink_of_three_thick`.  `coverDart`,
`thirdBase`, `thirdOp`, `rowL`, `rowT`, `rowR`, `rowS`, `rowOf`, `survRow`, `baseEnd`,
`opEnd`, `anchorBranch` name darts, rows and vertices already in hand, and `survEquiv`
inhabits an `Equiv` between two named four-element types.  No structure is introduced.

## Consumers

The `link` binder of `OuterWalk.coneEntry_of_reaches` at Part II case `{v2-nd4}`, and
the final valency dispatcher, through `link_of_valency_three`.  The census
`incidenceCount_anchor_eq_ends` and the matching `survEquiv` are the tools the
valency-three dispatcher needs in the same shape.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoDispatcher

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

noncomputable local instance instDecidableEqEdges (target : CFGraph) :
    DecidableEq target.edges := Classical.decEq _

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)


/-- A subtype of the elements of a finset cut out by a predicate is the filtered
finset. -/
theorem card_subtype_coe_filter {α : Type*} [DecidableEq α] (S : Finset α) (P : α → Prop)
    [DecidablePred P] : Fintype.card {x : ↥S // P x.1} = (S.filter P).card := by
  classical
  rw [← Fintype.card_coe]
  exact Fintype.card_congr
    { toFun := fun x ↦ ⟨x.1.1, Finset.mem_filter.mpr ⟨x.1.2, x.2⟩⟩
      invFun := fun y ↦ ⟨⟨y.1, (Finset.mem_filter.mp y.2).1⟩, (Finset.mem_filter.mp y.2).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-! ## 1.  The wall datum has path ends at every two-valent wall -/

theorem hasPathEnds_wall
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    HasPathEnds (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  WallDatumPathEnds.hasPathEnds_contractDatum wd.cover wd.fullDim wd.hc wd.hab wd.hOne
    (wd.hForest m) wd.coordinates (label m.base)
    (NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
      wallStar)
    wd.hZeroCoord wd.hPosCoord wd.hFacetZero

/-- The anchor of the wall datum, as a branch vertex. -/
def anchorBranch
    {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
    {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
  ⟨NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk, by
    rw [NonTrivalentValencyTwoTracks.nonDanglingValency_anchorVertex m wd src]
    omega⟩

@[simp] theorem anchorBranch_val
    {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
    {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
    (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk) :
    (anchorBranch m wd src).1 = NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk := rfl

/-! ## 2.  The row census at the two anchor ends -/

section Census

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {p q : wd.cover.SourceVertex}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
  (hEnds : NonTrivalentValencyTwoTracksLeaf.AnchorEnds m wd anchorBlk p q)

include src hOrd hEnds in
/-- **The row census at the two anchor ends.**  For every stable row of the wall
datum, the number of surviving occurrences at the anchor carrying that row is the
number of occurrences of its incoming row at the `A_u` end plus the number at the
`A_v` end.

The proof is a double count of `sum_incidenceCount_branchVertex` (`= 2` both
upstairs and downstairs) against the branch-vertex dictionary across the wall
contraction: away from the anchor the star of a row is unchanged (T2), the
branch vertices away from the anchor correspond to the branch vertices of the
incoming cover away from the two ends, and what is left over on the two sides of
the equation is exactly the claim.

Unlike `WallSplitIncidence.incidenceCount_anchor` this needs **no** hypothesis
that the anchor fibre is the two ends: the fibre may carry any number of
divalent pass-through vertices, and the count absorbs them, because a divalent
vertex is not a branch vertex on either side of the dictionary.  That is exactly
what makes it usable at the incomings with a pass-through survivor: the split
incomings of Configuration A and every Configuration B incoming. -/
theorem incidenceCount_anchor_eq_ends
    (row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) row =
      incidenceCount wd.cover p (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (wd.hCompat m) (wd.hForest m) row) +
        incidenceCount wd.cover q (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (wd.hCompat m) (wd.hForest m) row) := by
  classical
  set r := incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) row
    with hr
  set A : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) :=
    anchorBranch m wd src with hA
  -- the two sums of a stable row over its branch vertices
  have hUp : ∑ v : BranchVertex wd.cover, incidenceCount wd.cover v.1 r = 2 :=
    NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex wd.cover
      wd.fullDim.connected wd.fullDim.pathEnds r
  have hDown : ∑ w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne),
      incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w.1 row = 2 :=
    NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex
      (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (NonTrivalentValencyTwoTracks.wallValid m wd).1 (hasPathEnds_wall m wd wallStar) row
  -- upstairs: split off the two ends
  have hSplitUp : ∑ v : BranchVertex wd.cover, incidenceCount wd.cover v.1 r =
      (∑ v : {v : BranchVertex wd.cover // v.1 ≠ p ∧ v.1 ≠ q},
          incidenceCount wd.cover v.1.1 r) +
        (incidenceCount wd.cover p r + incidenceCount wd.cover q r) := by
    rw [← Equiv.sum_comp (NonTrivalentValencyTwoTracksLeaf.coverBranchEquiv m wd hEnds)
      (fun v : BranchVertex wd.cover ↦ incidenceCount wd.cover v.1 r), Fintype.sum_sum_type]
    congr 1
    rw [Fintype.sum_bool]
    show incidenceCount wd.cover q r + incidenceCount wd.cover p r = _
    omega
  -- downstairs: split off the anchor
  have hmem : ∀ w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne),
      w ∈ Finset.univ.erase A ↔
        w.1 ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk := by
    intro w
    rw [Finset.mem_erase]
    exact ⟨fun h ↦ fun hBad ↦ h.1 (Subtype.ext hBad),
      fun h ↦ ⟨fun hBad ↦ h (congrArg Subtype.val hBad), Finset.mem_univ _⟩⟩
  have hEraseDown : ∑ w ∈ Finset.univ.erase A,
        incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w.1 row =
      ∑ w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
          w.1 ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk},
        incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w.1.1 row :=
    Finset.sum_subtype _ hmem _
  have hAddDown := Finset.add_sum_erase
    (Finset.univ : Finset (BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)))
    (fun w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ↦
      incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w.1 row)
    (Finset.mem_univ A)
  -- the middle terms agree, by (T2) across the branch-vertex dictionary
  have hMiddle : (∑ v : {v : BranchVertex wd.cover // v.1 ≠ p ∧ v.1 ≠ q},
        incidenceCount wd.cover v.1.1 r) =
      ∑ w : {w : BranchVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) //
          w.1 ≠ NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk},
        incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) w.1.1 row := by
    refine Fintype.sum_equiv
      (NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement m wd hOrd hEnds) _ _
      (fun v ↦ ?_)
    exact (NonTrivalentValencyTwoStarCountAll.incidenceCount_wall_eq_incoming m wd src hOrd
      (NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement m wd hOrd hEnds v).1.1
      (NonTrivalentValencyTwoTracksLeaf.branchEquivAnchorComplement m wd hOrd hEnds v).2
      v.1.1 rfl v.1.2 row).symm
  show incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne) A.1 row = _
  omega

include hEnds in
/-- **The split of a row's branch-vertex incidences at the two anchor ends.** -/
theorem sum_split_ends (r : StablePath wd.cover) :
    ∑ v : BranchVertex wd.cover, incidenceCount wd.cover v.1 r =
      (∑ v : {v : BranchVertex wd.cover // v.1 ≠ p ∧ v.1 ≠ q},
          incidenceCount wd.cover v.1.1 r) +
        (incidenceCount wd.cover p r + incidenceCount wd.cover q r) := by
  classical
  rw [← Equiv.sum_comp (NonTrivalentValencyTwoTracksLeaf.coverBranchEquiv m wd hEnds)
    (fun v : BranchVertex wd.cover ↦ incidenceCount wd.cover v.1 r), Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_bool]
  show incidenceCount wd.cover q r + incidenceCount wd.cover p r = _
  omega

include hEnds in
/-- **A stable row of the incoming cover meets the two anchor ends at most twice in
all**: its total incidence over the branch vertices is two. -/
theorem incidenceCount_ends_le (r : StablePath wd.cover) :
    incidenceCount wd.cover p r + incidenceCount wd.cover q r ≤ 2 := by
  have h1 := sum_split_ends m wd hEnds r
  have h2 : ∑ v : BranchVertex wd.cover, incidenceCount wd.cover v.1 r = 2 :=
    NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex wd.cover
      wd.fullDim.connected wd.fullDim.pathEnds r
  omega

end Census

/-! ## 4.  The four darts the move sorts, and the two complementary pairs -/

section FourDarts

/-- The third dart of the ambient graph at `graph.vert m.base`. -/
def thirdBase : D :=
  Classical.choose (graph.exists_third (x := graph.vert m.base) rfl m.left_vert m.base_ne_left)

theorem thirdBase_vert : graph.vert (thirdBase m) = graph.vert m.base :=
  (Classical.choose_spec
    (graph.exists_third (x := graph.vert m.base) rfl m.left_vert m.base_ne_left)).1

theorem thirdBase_ne_base : thirdBase m ≠ m.base :=
  (Classical.choose_spec
    (graph.exists_third (x := graph.vert m.base) rfl m.left_vert m.base_ne_left)).2.1

theorem thirdBase_ne_left : thirdBase m ≠ m.left :=
  (Classical.choose_spec
    (graph.exists_third (x := graph.vert m.base) rfl m.left_vert m.base_ne_left)).2.2.1

theorem eq_base_or_left_or_thirdBase (z : D) (hz : graph.vert z = graph.vert m.base) :
    z = m.base ∨ z = m.left ∨ z = thirdBase m :=
  (Classical.choose_spec
    (graph.exists_third (x := graph.vert m.base) rfl m.left_vert m.base_ne_left)).2.2.2 z hz

/-- The third dart of the ambient graph at `graph.vert (graph.op m.base)`: the third
dart at the base end of the opposite description of the same move. -/
def thirdOp : D := thirdBase m.swap

theorem thirdOp_vert : graph.vert (thirdOp m) = graph.vert (graph.op m.base) :=
  thirdBase_vert m.swap

theorem thirdOp_ne_opBase : thirdOp m ≠ graph.op m.base := thirdBase_ne_base m.swap

theorem thirdOp_ne_right : thirdOp m ≠ m.right := thirdBase_ne_left m.swap

/-- **The moved star at `graph.vert m.base`.**  The move keeps `m.base` and the third
dart at that end and brings `m.right` over from the other end. -/
theorem movedStar_base :
    (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert m.base).erase m.base =
      {thirdBase m, m.right} := by
  classical
  ext d
  rw [IncomingPairing.mem_movedStar_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hdb, ⟨hdl, hdv⟩ | hdr⟩
    · rcases eq_base_or_left_or_thirdBase m d hdv with h | h | h
      · exact absurd h hdb
      · exact absurd h hdl
      · exact Or.inl h
    · exact Or.inr hdr
  · rintro (rfl | rfl)
    · exact ⟨thirdBase_ne_base m, Or.inl ⟨thirdBase_ne_left m, thirdBase_vert m⟩⟩
    · exact ⟨m.base_ne_right.symm, Or.inr rfl⟩

/-- **The moved star at `graph.vert (graph.op m.base)`**, the complementary pair: the
third dart at that end together with `m.left`. -/
theorem movedStar_op :
    (Finset.univ.filter fun d ↦ (graph.move m).vert d = graph.vert (graph.op m.base)).erase
        (graph.op m.base) = {thirdOp m, m.left} := by
  have h := movedStar_base m.swap
  rw [CubicDartGraph.move_swap] at h
  exact h

/-- **No Whitehead move is trivial.**  `CubicDarts.MoveData` carries `left ≠ base`,
`right ≠ op base` and `nonloop`, and the move sends the dart `m.left` to the *other* end
of the contracted edge, so `graph.move m` is never `graph`.  The case "the move does not
change the ambient graph" therefore does not arise in the walk's `link` binder, and the
dispatcher never has to produce a link for a trivial move. -/
theorem move_ne : graph.move m ≠ graph := by
  intro h
  have h1 : (graph.move m).vert m.left = graph.vert (graph.op m.base) := by
    show graph.vert (m.perm m.left) = _
    rw [m.perm_left, m.right_vert]
  rw [h] at h1
  exact m.nonloop (h1.symm.trans m.left_vert)

end FourDarts

/-! ## 3.  The two ends of the vanishing row, named by the move -/

section BaseEnds

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

/-- The end of the vanishing row at `graph.vert m.base`. -/
def baseEnd : wd.cover.SourceVertex := (IncomingPairing.baseDart m wd).1.1

/-- The end of the vanishing row at `graph.vert (graph.op m.base)`. -/
def opEnd : wd.cover.SourceVertex := (IncomingPairing.opBaseDart m wd).1.1

theorem baseEnd_ne_opEnd : baseEnd m wd ≠ opEnd m wd :=
  fun h ↦ IncomingPairing.vertex_baseDart_ne m wd (Subtype.ext h)

theorem incidenceCount_facetRow_baseEnd_pos :
    0 < incidenceCount wd.cover (baseEnd m wd) (NonTrivalentValencyTwoTracks.facetRow m wd) :=
  (incidenceCount_pos_iff _ _ _).mpr
    ⟨(IncomingPairing.baseDart m wd).2.1, (IncomingPairing.baseDart m wd).2.2,
      NonTrivalentValencyTwoBaseOneTracks.stablePath_baseDart m wd⟩

theorem incidenceCount_facetRow_opEnd_pos :
    0 < incidenceCount wd.cover (opEnd m wd) (NonTrivalentValencyTwoTracks.facetRow m wd) :=
  (incidenceCount_pos_iff _ _ _).mpr
    ⟨(IncomingPairing.opBaseDart m wd).2.1, (IncomingPairing.opBaseDart m wd).2.2,
      NonTrivalentValencyTwoBaseOneTracks.stablePath_opBaseDart m wd⟩

/-- **The two ends named by the move are the two anchor ends.**  Both are branch
vertices of the incoming cover meeting the vanishing row, so each is one of the
two ends of any `VanishingEnds`, and they are distinct because `m.base` is a
non-loop dart. -/
theorem anchorEnds_base
    (E : NonTrivalentValencyTwoStarCountAll.VanishingEnds m wd anchorBlk) :
    NonTrivalentValencyTwoTracksLeaf.AnchorEnds m wd anchorBlk (baseEnd m wd) (opEnd m wd) := by
  classical
  have hb : baseEnd m wd = E.left ∨ baseEnd m wd = E.right := by
    by_contra hc
    obtain ⟨h1, h2⟩ := not_or.mp hc
    have h := NonTrivalentValencyTwoStarCountAll.incidenceCount_facetRow_eq_zero m wd E
      (IncomingPairing.baseDart m wd).1 h1 h2
    have hpos : 0 < incidenceCount wd.cover ((IncomingPairing.baseDart m wd).1.1)
        (NonTrivalentValencyTwoTracks.facetRow m wd) := incidenceCount_facetRow_baseEnd_pos m wd
    omega
  have hq : opEnd m wd = E.left ∨ opEnd m wd = E.right := by
    by_contra hc
    obtain ⟨h1, h2⟩ := not_or.mp hc
    have h := NonTrivalentValencyTwoStarCountAll.incidenceCount_facetRow_eq_zero m wd E
      (IncomingPairing.opBaseDart m wd).1 h1 h2
    have hpos : 0 < incidenceCount wd.cover ((IncomingPairing.opBaseDart m wd).1.1)
        (NonTrivalentValencyTwoTracks.facetRow m wd) := incidenceCount_facetRow_opEnd_pos m wd
    omega
  have hne := baseEnd_ne_opEnd m wd
  rcases hb with hb | hb <;> rcases hq with hq | hq
  · exact absurd (hb.trans hq.symm) hne
  · rw [hb, hq]; exact E.ends
  · rw [hb, hq]; exact (NonTrivalentValencyTwoStarCountAll.swapEnds m wd E).ends
  · exact absurd (hb.trans hq.symm) hne

end BaseEnds

/-! ## 5.  The four rows at the two ends -/

section Rows

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}

theorem dart_eq_of_fst_of_edge (d d' : StableSourceDarts.Dart wd.cover)
    (h1 : d.1 = d'.1) (h2 : d.2.1 = d'.2.1) : d = d' := by
  obtain ⟨v, e⟩ := d
  obtain ⟨v', e'⟩ := d'
  cases h1
  exact congrArg _ (Subtype.ext h2)

/-- A dart of the ambient graph, read as a dart of the incoming cover. -/
def coverDart (z : D) : StableSourceDarts.Dart wd.cover := wd.tracks.iso.dart.symm z

@[simp] theorem dart_coverDart (z : D) : wd.tracks.iso.dart (coverDart m wd z) = z :=
  Equiv.apply_symm_apply _ _

theorem vtx_coverDart (z : D) :
    wd.tracks.iso.vtx (coverDart m wd z).1 = graph.vert z := by
  have h := wd.tracks.iso.vert_map (coverDart m wd z)
  rw [dart_coverDart] at h
  exact h.symm

theorem coverDart_fst_baseEnd (z : D) (hz : graph.vert z = graph.vert m.base) :
    (coverDart m wd z).1 = (IncomingPairing.baseDart m wd).1 :=
  wd.tracks.iso.vtx.injective
    ((vtx_coverDart m wd z).trans (hz.trans (IncomingPairing.vtx_baseDart m wd).symm))

theorem coverDart_fst_opEnd (z : D) (hz : graph.vert z = graph.vert (graph.op m.base)) :
    (coverDart m wd z).1 = (IncomingPairing.opBaseDart m wd).1 :=
  wd.tracks.iso.vtx.injective
    ((vtx_coverDart m wd z).trans (hz.trans (IncomingPairing.vtx_opBaseDart m wd).symm))

theorem coverDart_edge_ne_of_fst_eq {z z' : D} (hne : z ≠ z')
    (hfst : (coverDart m wd z).1 = (coverDart m wd z').1) :
    (coverDart m wd z).2.1 ≠ (coverDart m wd z').2.1 := by
  intro hBad
  exact hne (((dart_coverDart m wd z).symm.trans
    (congrArg wd.tracks.iso.dart (dart_eq_of_fst_of_edge m wd _ _ hfst hBad))).trans
    (dart_coverDart m wd z'))

/-- The occurrence of the vanishing row at the base end, read as `coverDart`. -/
theorem incident_coverDart (z : D) (v : wd.cover.SourceVertex)
    (hv : (coverDart m wd z).1.1 = v) :
    Incident wd.cover (coverDart m wd z).2.1.1 v := by
  cases hv
  exact (coverDart m wd z).2.2

theorem coverDart_base : coverDart m wd m.base = IncomingPairing.baseDart m wd := rfl

theorem coverDart_opBase : coverDart m wd (graph.op m.base) = IncomingPairing.opBaseDart m wd := rfl

/-- **The three surviving occurrences at the base end.** -/
theorem incidentEdges_baseEnd
    (hEnds : NonTrivalentValencyTwoTracksLeaf.AnchorEnds m wd anchorBlk
      (baseEnd m wd) (opEnd m wd)) :
    incidentEdges wd.cover (baseEnd m wd) =
      {(IncomingPairing.baseDart m wd).2.1, (coverDart m wd m.left).2.1,
        (coverDart m wd (thirdBase m)).2.1} := by
  classical
  have hL : (coverDart m wd m.left).1 = (IncomingPairing.baseDart m wd).1 :=
    coverDart_fst_baseEnd m wd _ m.left_vert
  have hT : (coverDart m wd (thirdBase m)).1 = (IncomingPairing.baseDart m wd).1 :=
    coverDart_fst_baseEnd m wd _ (thirdBase_vert m)
  have hB : (coverDart m wd m.base).1 = (IncomingPairing.baseDart m wd).1 := rfl
  have hBL := coverDart_edge_ne_of_fst_eq m wd m.base_ne_left (hB.trans hL.symm)
  have hBT := coverDart_edge_ne_of_fst_eq m wd (thirdBase_ne_base m).symm (hB.trans hT.symm)
  have hLT := coverDart_edge_ne_of_fst_eq m wd (thirdBase_ne_left m).symm (hL.trans hT.symm)
  have hNd : nonDanglingValency wd.cover (baseEnd m wd) = 3 := by
    have h1 := hEnds.2.1
    have h2 : nonDanglingValency wd.cover (baseEnd m wd) ≤ 3 := wd.fullDim.trivalent _
    omega
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    refine (mem_incidentEdges wd.cover _ e).mpr ?_
    rcases he with rfl | rfl | rfl
    · exact (IncomingPairing.baseDart m wd).2.2
    · exact incident_coverDart m wd _ _ (congrArg (fun b : BranchVertex wd.cover ↦ b.1) hL)
    · exact incident_coverDart m wd _ _ (congrArg (fun b : BranchVertex wd.cover ↦ b.1) hT)
  · rw [card_incidentEdges, hNd]
    refine le_of_eq (Finset.card_eq_three.mpr ⟨_, _, _, hBL, hBT, hLT, rfl⟩).symm

/-- **The three surviving occurrences at the op end.** -/
theorem incidentEdges_opEnd
    (hEnds : NonTrivalentValencyTwoTracksLeaf.AnchorEnds m wd anchorBlk
      (baseEnd m wd) (opEnd m wd)) :
    incidentEdges wd.cover (opEnd m wd) =
      {(IncomingPairing.opBaseDart m wd).2.1, (coverDart m wd m.right).2.1,
        (coverDart m wd (thirdOp m)).2.1} := by
  classical
  have hR : (coverDart m wd m.right).1 = (IncomingPairing.opBaseDart m wd).1 :=
    coverDart_fst_opEnd m wd _ m.right_vert
  have hS : (coverDart m wd (thirdOp m)).1 = (IncomingPairing.opBaseDart m wd).1 :=
    coverDart_fst_opEnd m wd _ (thirdOp_vert m)
  have hB : (coverDart m wd (graph.op m.base)).1 = (IncomingPairing.opBaseDart m wd).1 := rfl
  have hBR := coverDart_edge_ne_of_fst_eq m wd m.opBase_ne_right (hB.trans hR.symm)
  have hBS := coverDart_edge_ne_of_fst_eq m wd (thirdOp_ne_opBase m).symm (hB.trans hS.symm)
  have hRS := coverDart_edge_ne_of_fst_eq m wd (thirdOp_ne_right m).symm (hR.trans hS.symm)
  have hNd : nonDanglingValency wd.cover (opEnd m wd) = 3 := by
    have h1 := hEnds.2.2.1
    have h2 : nonDanglingValency wd.cover (opEnd m wd) ≤ 3 := wd.fullDim.trivalent _
    omega
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    refine (mem_incidentEdges wd.cover _ e).mpr ?_
    rcases he with rfl | rfl | rfl
    · exact (IncomingPairing.opBaseDart m wd).2.2
    · exact incident_coverDart m wd _ _ (congrArg (fun b : BranchVertex wd.cover ↦ b.1) hR)
    · exact incident_coverDart m wd _ _ (congrArg (fun b : BranchVertex wd.cover ↦ b.1) hS)
  · rw [card_incidentEdges, hNd]
    refine le_of_eq (Finset.card_eq_three.mpr ⟨_, _, _, hBR, hBS, hRS, rfl⟩).symm

/-- The row of the occurrence at the base end that the move sends away. -/
def rowL : StablePath wd.cover := (coverDart m wd m.left).2.1.stablePath

/-- The row of the occurrence at the base end that the move keeps. -/
def rowT : StablePath wd.cover := (coverDart m wd (thirdBase m)).2.1.stablePath

/-- The row of the occurrence at the op end that the move brings over. -/
def rowR : StablePath wd.cover := (coverDart m wd m.right).2.1.stablePath

/-- The row of the occurrence at the op end that the move keeps there. -/
def rowS : StablePath wd.cover := (coverDart m wd (thirdOp m)).2.1.stablePath

/-- The four rows the move sorts, indexed: `0` and `1` are the two occurrences at the
base end (the one the move sends away and the one it keeps), `2` and `3` the two at the
op end (the one it brings over and the one it keeps there). -/
def rowOf : Fin 4 → StablePath wd.cover
  | 0 => rowL m wd
  | 1 => rowT m wd
  | 2 => rowR m wd
  | 3 => rowS m wd

/-- The incoming row of a surviving occurrence of the wall datum. -/
def survRow (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    StablePath wd.cover :=
  incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) g.stablePath

variable (hEnds : NonTrivalentValencyTwoTracksLeaf.AnchorEnds m wd anchorBlk
    (baseEnd m wd) (opEnd m wd))

include hEnds in
/-- **The star of a row at the base end**, occurrence by occurrence. -/
theorem incidenceCount_baseEnd_eq (r : StablePath wd.cover) :
    incidenceCount wd.cover (baseEnd m wd) r =
      (if NonTrivalentValencyTwoTracks.facetRow m wd = r then 1 else 0) +
        ((if rowL m wd = r then 1 else 0) + (if rowT m wd = r then 1 else 0)) := by
  classical
  have hL : (coverDart m wd m.left).1 = (IncomingPairing.baseDart m wd).1 :=
    coverDart_fst_baseEnd m wd _ m.left_vert
  have hT : (coverDart m wd (thirdBase m)).1 = (IncomingPairing.baseDart m wd).1 :=
    coverDart_fst_baseEnd m wd _ (thirdBase_vert m)
  have hB : (coverDart m wd m.base).1 = (IncomingPairing.baseDart m wd).1 := rfl
  have hBL := coverDart_edge_ne_of_fst_eq m wd m.base_ne_left (hB.trans hL.symm)
  have hBT := coverDart_edge_ne_of_fst_eq m wd (thirdBase_ne_base m).symm (hB.trans hT.symm)
  have hLT := coverDart_edge_ne_of_fst_eq m wd (thirdBase_ne_left m).symm (hL.trans hT.symm)
  unfold incidenceCount
  rw [incidentEdges_baseEnd m wd hEnds, Finset.card_filter,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact not_or.mpr ⟨hBL, hBT⟩),
    Finset.sum_insert (by simpa using hLT), Finset.sum_singleton,
    NonTrivalentValencyTwoBaseOneTracks.stablePath_baseDart m wd]
  rfl

include hEnds in
/-- **The star of a row at the op end**, occurrence by occurrence. -/
theorem incidenceCount_opEnd_eq (r : StablePath wd.cover) :
    incidenceCount wd.cover (opEnd m wd) r =
      (if NonTrivalentValencyTwoTracks.facetRow m wd = r then 1 else 0) +
        ((if rowR m wd = r then 1 else 0) + (if rowS m wd = r then 1 else 0)) := by
  classical
  have hR : (coverDart m wd m.right).1 = (IncomingPairing.opBaseDart m wd).1 :=
    coverDart_fst_opEnd m wd _ m.right_vert
  have hS : (coverDart m wd (thirdOp m)).1 = (IncomingPairing.opBaseDart m wd).1 :=
    coverDart_fst_opEnd m wd _ (thirdOp_vert m)
  have hB : (coverDart m wd (graph.op m.base)).1 = (IncomingPairing.opBaseDart m wd).1 := rfl
  have hBR := coverDart_edge_ne_of_fst_eq m wd m.opBase_ne_right (hB.trans hR.symm)
  have hBS := coverDart_edge_ne_of_fst_eq m wd (thirdOp_ne_opBase m).symm (hB.trans hS.symm)
  have hRS := coverDart_edge_ne_of_fst_eq m wd (thirdOp_ne_right m).symm (hR.trans hS.symm)
  unfold incidenceCount
  rw [incidentEdges_opEnd m wd hEnds, Finset.card_filter,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact not_or.mpr ⟨hBR, hBS⟩),
    Finset.sum_insert (by simpa using hRS), Finset.sum_singleton,
    NonTrivalentValencyTwoBaseOneTracks.stablePath_opBaseDart m wd]
  rfl

include hEnds in
/-- **None of the four rows is the vanishing row.**  The vanishing row meets each end
exactly once, through the dart of the contracted edge. -/
theorem rows_ne_facetRow :
    rowL m wd ≠ NonTrivalentValencyTwoTracks.facetRow m wd ∧
      rowT m wd ≠ NonTrivalentValencyTwoTracks.facetRow m wd ∧
        rowR m wd ≠ NonTrivalentValencyTwoTracks.facetRow m wd ∧
          rowS m wd ≠ NonTrivalentValencyTwoTracks.facetRow m wd := by
  classical
  have hBase := incidenceCount_baseEnd_eq m wd hEnds (NonTrivalentValencyTwoTracks.facetRow m wd)
  have hOp := incidenceCount_opEnd_eq m wd hEnds (NonTrivalentValencyTwoTracks.facetRow m wd)
  have hLe := incidenceCount_ends_le m wd hEnds (NonTrivalentValencyTwoTracks.facetRow m wd)
  rw [if_pos rfl] at hBase hOp
  refine ⟨fun hBad ↦ ?_, fun hBad ↦ ?_, fun hBad ↦ ?_, fun hBad ↦ ?_⟩
  · rw [if_pos hBad] at hBase; omega
  · rw [if_pos hBad] at hBase; omega
  · rw [if_pos hBad] at hOp; omega
  · rw [if_pos hBad] at hOp; omega

/-! ## 6.  The census as a fibrewise count of the four rows -/

section Fibres

variable (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

theorem incomingRow_ne_facetRow (row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne)) :
    incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) row ≠
      NonTrivalentValencyTwoTracks.facetRow m wd :=
  incomingRow_ne_facet wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
    wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero row

include hEnds in
theorem nonDanglingValency_baseEnd : nonDanglingValency wd.cover (baseEnd m wd) = 3 := by
  have h1 := hEnds.2.1
  have h2 : nonDanglingValency wd.cover (baseEnd m wd) ≤ 3 := wd.fullDim.trivalent _
  omega

include hEnds in
theorem nonDanglingValency_opEnd : nonDanglingValency wd.cover (opEnd m wd) = 3 := by
  have h1 := hEnds.2.2.1
  have h2 : nonDanglingValency wd.cover (opEnd m wd) ≤ 3 := wd.fullDim.trivalent _
  omega

include hEnds in
/-- The vanishing row meets each of the two ends exactly once. -/
theorem incidenceCount_facetRow_ends :
    incidenceCount wd.cover (baseEnd m wd) (NonTrivalentValencyTwoTracks.facetRow m wd) +
      incidenceCount wd.cover (opEnd m wd) (NonTrivalentValencyTwoTracks.facetRow m wd) = 2 := by
  classical
  obtain ⟨hL, hT, hR, hS⟩ := rows_ne_facetRow m wd hEnds
  have hBase := incidenceCount_baseEnd_eq m wd hEnds (NonTrivalentValencyTwoTracks.facetRow m wd)
  have hOp := incidenceCount_opEnd_eq m wd hEnds (NonTrivalentValencyTwoTracks.facetRow m wd)
  rw [if_pos rfl, if_neg hL, if_neg hT] at hBase
  rw [if_pos rfl, if_neg hR, if_neg hS] at hOp
  omega

include src hOrd hEnds in
/-- **A row that is not an incoming row meets neither end.**  Both sides of the census
add up to the surviving valency four of the anchor, and the incoming-row map is an
injection into the rows other than the vanishing one, so nothing is left over. -/
theorem incidenceCount_ends_eq_zero_of_not_incomingRow (r : StablePath wd.cover)
    (hr : r ≠ NonTrivalentValencyTwoTracks.facetRow m wd)
    (hnot : ∀ row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
      incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) row ≠ r) :
    incidenceCount wd.cover (baseEnd m wd) r + incidenceCount wd.cover (opEnd m wd) r = 0 := by
  classical
  set F := incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m)
    with hF
  set g : StablePath wd.cover → ℕ := fun t ↦
    incidenceCount wd.cover (baseEnd m wd) t + incidenceCount wd.cover (opEnd m wd) t with hg
  have hInj : Function.Injective F :=
    NonTrivalentValencyTwoStarCountAll.injective_incomingRow m wd wallStar
  have hImage : (Finset.univ.image F) ⊆
      Finset.univ.erase (NonTrivalentValencyTwoTracks.facetRow m wd) := by
    intro t ht
    obtain ⟨row, -, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_erase.mpr ⟨incomingRow_ne_facetRow m wd row, Finset.mem_univ _⟩
  have hSumImage : ∑ t ∈ Finset.univ.image F, g t = 4 := by
    rw [Finset.sum_image (fun x _ y _ h ↦ hInj h)]
    have hCensus : ∀ row, g (F row) =
        incidenceCount (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) row :=
      fun row ↦ (incidenceCount_anchor_eq_ends m wd src hOrd hEnds row).symm
    rw [Finset.sum_congr rfl (fun row _ ↦ hCensus row)]
    rw [sum_incidenceCount_vertex,
      NonTrivalentValencyTwoTracks.nonDanglingValency_anchorVertex m wd src]
  have hSumAll : ∑ t : StablePath wd.cover, g t = 6 := by
    rw [hg]
    rw [Finset.sum_add_distrib, sum_incidenceCount_vertex, sum_incidenceCount_vertex,
      nonDanglingValency_baseEnd m wd hEnds, nonDanglingValency_opEnd m wd hEnds]
  have hSumErase : ∑ t ∈ Finset.univ.erase (NonTrivalentValencyTwoTracks.facetRow m wd), g t
      = 4 := by
    have h := Finset.add_sum_erase (Finset.univ : Finset (StablePath wd.cover)) g
      (Finset.mem_univ (NonTrivalentValencyTwoTracks.facetRow m wd))
    have hFacet : g (NonTrivalentValencyTwoTracks.facetRow m wd) = 2 :=
      incidenceCount_facetRow_ends m wd hEnds
    omega
  have hSdiff := Finset.sum_sdiff (f := g) hImage
  have hMem : r ∈ (Finset.univ.erase (NonTrivalentValencyTwoTracks.facetRow m wd)) \
      (Finset.univ.image F) := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩, ?_⟩
    intro hBad
    obtain ⟨row, -, hrow⟩ := Finset.mem_image.mp hBad
    exact hnot row hrow
  have hLe := Finset.single_le_sum (f := g) (fun t _ ↦ Nat.zero_le (g t)) hMem
  have hzero : g r = 0 := by omega
  exact hzero

include src hOrd hEnds in
/-- **The census, fibre by fibre.**  For every stable row `r` of the incoming cover the
number of surviving occurrences at the anchor whose incoming row is `r` is the number of
the four non-vanishing occurrences at the two ends carrying `r`. -/
theorem card_filter_anchor_eq (r : StablePath wd.cover) :
    ((incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)).filter
        (fun g ↦ survRow m wd g = r)).card =
      ((if rowL m wd = r then 1 else 0) + (if rowT m wd = r then 1 else 0)) +
        ((if rowR m wd = r then 1 else 0) + (if rowS m wd = r then 1 else 0)) := by
  classical
  obtain ⟨hL, hT, hR, hS⟩ := rows_ne_facetRow m wd hEnds
  by_cases hr : r = NonTrivalentValencyTwoTracks.facetRow m wd
  · subst hr
    rw [if_neg hL, if_neg hT, if_neg hR, if_neg hS]
    refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
    intro g _
    exact incomingRow_ne_facetRow m wd g.stablePath
  · have hEq : ((if rowL m wd = r then 1 else 0) + (if rowT m wd = r then 1 else 0)) +
        ((if rowR m wd = r then 1 else 0) + (if rowS m wd = r then 1 else 0)) =
        incidenceCount wd.cover (baseEnd m wd) r + incidenceCount wd.cover (opEnd m wd) r := by
      rw [incidenceCount_baseEnd_eq m wd hEnds r, incidenceCount_opEnd_eq m wd hEnds r,
        if_neg (show ¬(NonTrivalentValencyTwoTracks.facetRow m wd = r) from fun h ↦ hr h.symm)]
      omega
    rw [hEq]
    by_cases hex : ∃ row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
        incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
          (wd.hForest m) row = r
    · obtain ⟨row, hrow⟩ := hex
      have hInj : Function.Injective (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (wd.hCompat m) (wd.hForest m)) :=
        NonTrivalentValencyTwoStarCountAll.injective_incomingRow m wd wallStar
      have hFilter : ((incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)).filter
          (fun g ↦ survRow m wd g = r)) =
          ((incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)).filter
          (fun g ↦ g.stablePath = row)) := by
        refine Finset.filter_congr (fun g _ ↦ ?_)
        constructor
        · intro h
          exact hInj (h.trans hrow.symm)
        · intro h
          exact (congrArg (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
            (wd.hCompat m) (wd.hForest m)) h).trans hrow
      rw [hFilter]
      exact (incidenceCount_anchor_eq_ends m wd src hOrd hEnds row).trans (by rw [hrow])
    · have hex' : ∀ row : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
          incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hCompat m)
            (wd.hForest m) row ≠ r := fun row hrow ↦ hex ⟨row, hrow⟩
      rw [incidenceCount_ends_eq_zero_of_not_incomingRow m wd hEnds src hOrd r hr hex']
      refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
      intro g _
      exact hex' g.stablePath

end Fibres

/-! ## 7.  The row-preserving bijection between the four darts and the four survivors -/

section Bijection

variable (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)

theorem card_fibre_rowOf (r : StablePath wd.cover) :
    Fintype.card {i : Fin 4 // rowOf m wd i = r} =
      ((if rowL m wd = r then 1 else 0) + (if rowT m wd = r then 1 else 0)) +
        ((if rowR m wd = r then 1 else 0) + (if rowS m wd = r then 1 else 0)) := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_four]
  show (if rowL m wd = r then 1 else 0) + (if rowT m wd = r then 1 else 0) +
    (if rowR m wd = r then 1 else 0) + (if rowS m wd = r then 1 else 0) = _
  omega

theorem card_fibre_survRow (r : StablePath wd.cover) :
    Fintype.card {x : ↥(incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)) // survRow m wd x.1 = r} =
      ((incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)).filter
        (fun g ↦ survRow m wd g = r)).card := by
  classical
  rw [← Fintype.card_coe]
  exact Fintype.card_congr
    { toFun := fun x ↦ ⟨x.1.1, Finset.mem_filter.mpr ⟨x.1.2, x.2⟩⟩
      invFun := fun y ↦ ⟨⟨y.1, (Finset.mem_filter.mp y.2).1⟩, (Finset.mem_filter.mp y.2).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

include src hOrd hEnds in
theorem card_fibre_eq (r : StablePath wd.cover) :
    Fintype.card {i : Fin 4 // rowOf m wd i = r} =
      Fintype.card {x : ↥(incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)) // survRow m wd x.1 = r} := by
  rw [card_fibre_rowOf, card_fibre_survRow, card_filter_anchor_eq m wd hEnds src hOrd r]

/-- **The row-preserving bijection.**  The four occurrences the move sorts at the two ends
of the vanishing row correspond to the four surviving occurrences of the wall datum at the
anchor, occurrence for occurrence, each carrying the same stable row of the incoming
cover.  This is the census read as a matching. -/
def survEquiv : Fin 4 ≃ ↥(incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)) :=
  (Equiv.sigmaFiberEquiv (rowOf m wd)).symm.trans
    ((Equiv.sigmaCongrRight fun r ↦
        (Fintype.card_eq.mp (card_fibre_eq m wd hEnds src hOrd r)).some).trans
      (Equiv.sigmaFiberEquiv
        (fun x : ↥(incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)) ↦ survRow m wd x.1)))

theorem survRow_survEquiv (i : Fin 4) :
    survRow m wd (survEquiv m wd hEnds src hOrd i).1 = rowOf m wd i :=
  ((Equiv.sigmaCongrRight fun r ↦ (Fintype.card_eq.mp (card_fibre_eq m wd hEnds src hOrd r)).some)
    ((Equiv.sigmaFiberEquiv (rowOf m wd)).symm i)).2.2

theorem incident_survEquiv (i : Fin 4) :
    Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) (survEquiv m wd hEnds src hOrd i).1.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) :=
  (mem_incidentEdges _ _ _).mp (survEquiv m wd hEnds src hOrd i).2

/-- The predicate picking out the survivors over the thick target direction. -/
abbrev IsThickSurv (star : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (g : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)) : Prop :=
  (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) =
    Prescribed.thickEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne) star blk

/-- The thick survivors at the anchor, counted among the surviving occurrences. -/
theorem card_filter_thick :
    ((incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)).filter
        (fun g ↦ IsThickSurv m wd wallStar anchorBlk g)).card =
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (Prescribed.thickDirection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlk)).card := by
  classical
  refine Finset.card_bij
    (fun g hg ↦ (⟨g.1, (mem_incidentEdges _ _ _).mp (Finset.mem_filter.mp hg).1⟩ :
      IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩ anchorBlk))) ?_ ?_ ?_
  · intro g hg
    exact (mem_directionSurvivors _ _ _ _ _).mpr
      ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g.2, (Finset.mem_filter.mp hg).2⟩
  · intro g₁ h₁ g₂ h₂ hEq
    exact Subtype.ext (congrArg (fun e : IncidentSourceEdge
      (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ anchorBlk) ↦ e.1) hEq)
  · intro e he
    obtain ⟨hSurv, hTarget⟩ := (mem_directionSurvivors _ _ _ _ _).mp he
    refine ⟨⟨e.1, (W3R1SourceProfile.mem_survivors _ _ _).mp hSurv⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr e.2, hTarget⟩

/-- **The thick positions are counted by the thick direction.**  Through the census
bijection, the positions whose survivor lies over the thick direction are as many as the
survivors of the thick direction. -/
theorem card_thickPos_eq :
    (Finset.univ.filter fun i : Fin 4 ↦
        IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd i).1).card =
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (Prescribed.thickDirection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlk)).card := by
  classical
  have h1 : Fintype.card {i : Fin 4 //
        IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd i).1} =
      Fintype.card {x : ↥(incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)) //
        IsThickSurv m wd wallStar anchorBlk x.1} :=
    Fintype.card_congr (Equiv.subtypeEquiv (survEquiv m wd hEnds src hOrd) fun _ ↦ Iff.rfl)
  have h2 : Fintype.card {i : Fin 4 //
        IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd i).1} =
      (Finset.univ.filter fun i : Fin 4 ↦
        IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd i).1).card :=
    Fintype.card_subtype _
  have h3 : Fintype.card {x : ↥(incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)) //
        IsThickSurv m wd wallStar anchorBlk x.1} =
      ((incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)).filter
        (fun g ↦ IsThickSurv m wd wallStar anchorBlk g)).card :=
    card_subtype_coe_filter _ _
  have h4 : ((incidentEdges (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk)).filter
        (fun g ↦ IsThickSurv m wd wallStar anchorBlk g)).card =
      (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk
        (Prescribed.thickDirection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlk)).card := card_filter_thick m wd
  omega

/-- **At least two of the four positions are thick.**  Both the `2 + 2` and the `3 + 1`
distribution leave at least two survivors over the thick direction
(`NonTrivalentValencyTwoCandidate.Prescribed.two_le_card_thick`). -/
theorem two_le_card_thickPos :
    2 ≤ (Finset.univ.filter fun i : Fin 4 ↦
      IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd i).1).card := by
  rw [card_thickPos_eq m wd hEnds src hOrd]
  exact Prescribed.two_le_card_thick src

/-- **The three ways the move can meet the thick direction.**  Either the two
occurrences it brings together (positions `1` and `2`) both lie over the thick
direction -- a same-direction pair, closed by the merge; or the two occurrences the
opposite description of the move brings together (positions `3` and `0`) do; or the
move's own pair is a cross pair, one member over each direction, and then the
complementary pair is a cross pair too. -/
theorem thick_trichotomy :
    (IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 1).1 ∧
        IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 2).1) ∨
      (IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 3).1 ∧
          IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 0).1) ∨
        (((IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 1).1 ∧
              ¬ IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 2).1) ∨
            (IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 2).1 ∧
              ¬ IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 1).1)) ∧
          (¬ IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 3).1 ∨
            ¬ IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 0).1)) := by
  classical
  by_cases hA : IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 1).1 ∧
      IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 2).1
  · exact Or.inl hA
  · by_cases hB : IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 3).1 ∧
        IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 0).1
    · exact Or.inr (Or.inl hB)
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · by_cases h1 : IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 1).1
        · exact Or.inl ⟨h1, fun h2 ↦ hA ⟨h1, h2⟩⟩
        · by_cases h2 : IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 2).1
          · exact Or.inr ⟨h2, h1⟩
          · exfalso
            have hsub : (Finset.univ.filter fun i : Fin 4 ↦
                IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd i).1) ⊆
                ({0, 3} : Finset (Fin 4)) := by
              intro i hi
              have hT := (Finset.mem_filter.mp hi).2
              fin_cases i
              · exact Finset.mem_insert_self _ _
              · exact absurd hT h1
              · exact absurd hT h2
              · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            have hcard : ({0, 3} : Finset (Fin 4)).card ≤ (Finset.univ.filter fun i : Fin 4 ↦
                IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd i).1).card := by
              have h := two_le_card_thickPos m wd hEnds src hOrd
              have hc : ({0, 3} : Finset (Fin 4)).card = 2 := by decide
              omega
            have heq := Finset.eq_of_subset_of_card_le hsub hcard
            have h3 : (3 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) :=
              Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            have h0 : (0 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) := Finset.mem_insert_self _ _
            rw [← heq] at h3 h0
            exact hB ⟨(Finset.mem_filter.mp h3).2, (Finset.mem_filter.mp h0).2⟩
      · by_cases h3 : IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd 3).1
        · exact Or.inr fun h0 ↦ hB ⟨h3, h0⟩
        · exact Or.inl h3

/-- **A `3 + 1` wall has no cross pair.**  With three survivors over the thick direction
at most one of the four positions is thin, so the move's own pair or the complementary
pair is a same-direction pair. -/
theorem not_cross_of_three_thick
    (h3 : 3 ≤ (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
      anchorBlk (Prescribed.thickDirection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        wallStar anchorBlk)).card)
    {i j : Fin 4} (hij : i ≠ j)
    (hi : ¬ IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd i).1)
    (hj : ¬ IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd j).1) :
    False := by
  classical
  have hsub : ({i, j} : Finset (Fin 4)) ⊆ Finset.univ.filter (fun k : Fin 4 ↦
      ¬ IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd k).1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hle : ({i, j} : Finset (Fin 4)).card ≤ (Finset.univ.filter (fun k : Fin 4 ↦
      ¬ IsThickSurv m wd wallStar anchorBlk (survEquiv m wd hEnds src hOrd k).1)).card :=
    Finset.card_le_card hsub
  rw [Finset.card_pair hij] at hle
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4)))
    (p := fun k : Fin 4 ↦ IsThickSurv m wd wallStar anchorBlk
      (survEquiv m wd hEnds src hOrd k).1)
  have hcard : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  rw [card_thickPos_eq m wd hEnds src hOrd] at hsum
  omega

end Bijection

end Rows

/-! ## 8.  The merge: the link at a same-direction pair -/

section Merge

variable {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩ anchorBlk)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted})
  (hRowVal : ∀ pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
    (labelling₀.row pth).1 =
      Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) pth)))
  (hMatrixWall : ∀ (pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (column : {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}),
    GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row pth) column =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) pth)) column.1)

include src hOrd labelling₀ hRowVal hMatrixWall in
/-- **The link when the two survivors the move brings together lie over the *same*
target direction** -- the Base II merge.  Nothing but the wall data and the two named
survivors enters: the headline of `NonTrivalentValencyTwoStarCountAll` turns (H-II) into
the link at any two-valent Base II wall, and (H-II) is discharged here from the moved star
(`IncomingPairing.exists_movedStar_darts` in the explicit form `movedStar_base`). -/
theorem nonempty_typeChangeLink_of_thick_rows
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hg : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hg' : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
      (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk))
    (hne : g ≠ g')
    (hgT : IsThickSurv m wd wallStar anchorBlk g)
    (hgT' : IsThickSurv m wd wallStar anchorBlk g')
    (hrow : survRow m wd g = rowT m wd) (hrow' : survRow m wd g' = rowR m wd) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  refine NonTrivalentValencyTwoStarCountAll.nonempty_typeChangeLink_of_prescribedMergedMoveAny m wd src
    { first := ⟨g.1, hg⟩
      second := ⟨g'.1, hg'⟩
      first_ne_second := fun h ↦ hne (Subtype.ext (congrArg
        (fun e : IncidentSourceEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (NonTrivalentValencyTwoTracks.anchorVertex m wd anchorBlk) ↦ e.1) h))
      first_mem := (mem_directionSurvivors _ _ _ _ _).mpr
        ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g.2, hgT⟩
      second_mem := (mem_directionSurvivors _ _ _ _ _).mpr
        ⟨(W3R1SourceProfile.mem_survivors _ _ _).mpr g'.2, hgT'⟩ }
    hOrd labelling₀ hRowVal hMatrixWall ?_
  refine NonTrivalentValencyTwoStarCountAll.prescribedMergedMoveAny_of_rows m wd _
    ⟨(IncomingPairing.baseDart m wd).1, (IncomingPairing.opBaseDart m wd).1,
      incidenceCount_facetRow_baseEnd_pos m wd, incidenceCount_facetRow_opEnd_pos m wd,
      (IncomingPairing.vtx_baseDart m wd).symm, (IncomingPairing.vtx_opBaseDart m wd).symm⟩
    (coverDart m wd (thirdBase m)) (coverDart m wd m.right) ?_ ?_ ?_
  · exact hrow.symm
  · exact hrow'.symm
  · rw [movedStar_base m, dart_coverDart, dart_coverDart]

end Merge

/-! ## 9.  The headline at a two-valent wall -/

section Headline

/-- **The valency-two dispatch.**  At every two-valent wall datum, either the link is
already there -- the two survivors the move brings together lie over the same target
direction, so the Base II merge realises it, possibly after re-reading the move from the
other end of the contracted edge (`CubicDarts.MoveData.swap`) -- or the wall carries the
Configuration A `2 + 2` distribution and the move names a **cross pair**: one survivor
over each direction, whose incoming rows are the rows of the two occurrences the move
brings together, in one of the two orders.

This is the whole content of the dispatcher: the census
(`incidenceCount_anchor_eq_ends`) matches the four occurrences the move sorts at the two
ends of the vanishing row with the four survivors at the anchor, and at least two
survivors lie over the thick direction. -/
theorem link_or_crossPair
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) :
    Nonempty (TypeChangeLink m wd) ∨
      ∃ (blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
        (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)),
        TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne)
            (TwoStar.of_card h2) blk ∧
          (∀ direction : Fin 2, (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              (TwoStar.of_card h2) blk direction).card = 2) ∧
            Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
                (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
                  ⟨wd.a, wd.hab⟩ blk) ∧
              Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
                  (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
                    ⟨wd.a, wd.hab⟩ blk) ∧
                (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) ≠ g'.1.1.1 ∧
                  ((survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
                    (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd)) := by
  classical
  set wallStar := TwoStar.of_card (target := contract wd.coverTarget wd.hab wd.hOne)
    (wall := ⟨wd.a, wd.hab⟩) h2 with hwallStar
  obtain ⟨anchorBlock, hNd, src⟩ :=
    NonTrivalentAnchorValency.twoBranchAnchor_of_single_row wd.cover wd.fullDim wd.hc wd.hab
      wd.hOne (wd.hForest m) wd.coordinates (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord
      wd.hFacetZero wallStar
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base)
    wd.hRows wd.hZeroCoord anchorBlock hNd
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨E⟩ := NonTrivalentValencyTwoStarCountAll.nonempty_vanishingEnds m wd src hOrd
  have hEnds := anchorEnds_base m wd E
  have hInj : ∀ i j : Fin 4, i ≠ j →
      (survEquiv m wd hEnds src hOrd i).1 ≠ (survEquiv m wd hEnds src hOrd j).1 := by
    intro i j hij hBad
    exact hij ((survEquiv m wd hEnds src hOrd).injective (Subtype.ext hBad))
  -- the `2 + 2` fact in the cross case
  have hTwoTwo : ∀ {i j : Fin 4}, i ≠ j →
      ¬ IsThickSurv m wd wallStar anchorBlock (survEquiv m wd hEnds src hOrd i).1 →
      ¬ IsThickSurv m wd wallStar anchorBlock (survEquiv m wd hEnds src hOrd j).1 →
      ∀ direction : Fin 2,
        (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock direction).card = 2 := by
    intro i j hij hi hj
    have hsub : ({i, j} : Finset (Fin 4)) ⊆ Finset.univ.filter (fun k : Fin 4 ↦
        ¬ IsThickSurv m wd wallStar anchorBlock (survEquiv m wd hEnds src hOrd k).1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hle : ({i, j} : Finset (Fin 4)).card ≤ (Finset.univ.filter (fun k : Fin 4 ↦
        ¬ IsThickSurv m wd wallStar anchorBlock (survEquiv m wd hEnds src hOrd k).1)).card :=
      Finset.card_le_card hsub
    rw [Finset.card_pair hij] at hle
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 4)))
      (p := fun k : Fin 4 ↦ IsThickSurv m wd wallStar anchorBlock
        (survEquiv m wd hEnds src hOrd k).1)
    have hcard : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    rw [card_thickPos_eq m wd hEnds src hOrd] at hsum
    have hge := Prescribed.two_le_card_thick src
    have hthick : (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlock (Prescribed.thickDirection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlock)).card = 2 := by omega
    have hsplit := Prescribed.card_thick_add_card_thin src
    have hthin : (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlock (Prescribed.thinDirection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlock)).card = 2 := by omega
    intro direction
    by_cases hd : direction = Prescribed.thickDirection
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock
    · rw [hd]; exact hthick
    · have hd' : direction = Prescribed.thickDirection
          (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlock + 1 := by
        revert hd
        generalize (Prescribed.thickDirection (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          wallStar anchorBlock) = t
        revert direction t
        decide
      rw [hd']; exact hthin
  rcases thick_trichotomy m wd hEnds src hOrd with ⟨ht1, ht2⟩ | ⟨ht3, ht0⟩ |
    ⟨(⟨ht1, ht2⟩ | ⟨ht2, ht1⟩), hOther⟩
  · exact Or.inl (nonempty_typeChangeLink_of_thick_rows m wd src hOrd labelling₀ hRowVal
      hMatrixWall _ _ (incident_survEquiv m wd hEnds src hOrd 1)
      (incident_survEquiv m wd hEnds src hOrd 2) (hInj 1 2 (by decide)) ht1 ht2
      (survRow_survEquiv m wd hEnds src hOrd 1) (survRow_survEquiv m wd hEnds src hOrd 2))
  · have hL : label (graph.op m.base) = label m.base :=
      MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base
    have hRowVal' : ∀ pth : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
        (labelling₀.row pth).1 =
          Equiv.swap (label (graph.op m.base))
            (wd.fullDim.labelling.targetEdge.symm wd.contracted)
            (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
              (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
                wd.hOne (wd.hForest m)) (wd.hForest m) pth)) := by
      intro pth
      rw [hL]
      exact hRowVal pth
    exact Or.inl ((nonempty_typeChangeLink_of_thick_rows m.swap
      (NonTrivalentValencyFourDispatcher.swapWallData m wd hL) src hOrd labelling₀ hRowVal'
      hMatrixWall _ _ (incident_survEquiv m wd hEnds src hOrd 3)
      (incident_survEquiv m wd hEnds src hOrd 0) (hInj 3 0 (by decide)) ht3 ht0
      (survRow_survEquiv m wd hEnds src hOrd 3)
      (survRow_survEquiv m wd hEnds src hOrd 0)).map
      (NonTrivalentValencyFourDispatcher.linkOfSwap m wd hL))
  · refine Or.inr ⟨anchorBlock, _, _, src, ?_, incident_survEquiv m wd hEnds src hOrd 1,
      incident_survEquiv m wd hEnds src hOrd 2, ?_,
      Or.inl ⟨survRow_survEquiv m wd hEnds src hOrd 1, survRow_survEquiv m wd hEnds src hOrd 2⟩⟩
    · rcases hOther with h | h
      · exact hTwoTwo (by decide : (2 : Fin 4) ≠ 3) ht2 h
      · exact hTwoTwo (by decide : (2 : Fin 4) ≠ 0) ht2 h
    · intro hBad
      exact ht2 (hBad.symm.trans ht1)
  · refine Or.inr ⟨anchorBlock, _, _, src, ?_, incident_survEquiv m wd hEnds src hOrd 2,
      incident_survEquiv m wd hEnds src hOrd 1, ?_,
      Or.inr ⟨survRow_survEquiv m wd hEnds src hOrd 2, survRow_survEquiv m wd hEnds src hOrd 1⟩⟩
    · rcases hOther with h | h
      · exact hTwoTwo (by decide : (1 : Fin 4) ≠ 3) ht1 h
      · exact hTwoTwo (by decide : (1 : Fin 4) ≠ 0) ht1 h
    · intro hBad
      exact ht1 (hBad.symm.trans ht2)

/-- **(H-cross), the cross-pair hypothesis** -- the only input of the valency-two
dispatcher not proved in this module.  The two survivors of the wall datum that the
Whitehead move brings together lie over *different* target directions at a `2 + 2`
Configuration A wall, and their incoming rows are the rows of the two occurrences the
move names.  By the closing count of the valency-two analysis in Part II, Section 5.4,
exactly one of the Base I member (when the two index equalities hold) and the
Configuration A split member (when they fail) realises such a pairing. -/
def CrossPairLink
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) : Prop :=
  ∀ (blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)),
    TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk →
      (∀ direction : Fin 2, (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (TwoStar.of_card h2) blk direction).card = 2) →
        Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ blk) →
          Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
              (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
                ⟨wd.a, wd.hab⟩ blk) →
            (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) ≠ g'.1.1.1 →
              ((survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
                (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd)) →
                Nonempty (TypeChangeLink m wd)

/-- **`OuterWalk.TypeChangeLink` at every two-valent wall datum of every Whitehead move,
modulo the cross-pair hypothesis.** -/
theorem typeChangeLink_two
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (hCross : CrossPairLink m wd h2) : Nonempty (TypeChangeLink m wd) := by
  rcases link_or_crossPair m wd h2 with h | ⟨blk, g, g', hsrc, hsplit, hg, hg', hne, hrows⟩
  · exact h
  · exact hCross blk g g' hsrc hsplit hg hg' hne hrows

/-- **At a `3 + 1` wall every move is closed, with no hypothesis beyond the
distribution.**  Three survivors over the thick direction leave at most one thin
position, so a cross pair is impossible and the merge always applies. -/
theorem typeChangeLink_two_of_three_thick
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (h3 : ∀ blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩,
      TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk →
        3 ≤ (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (TwoStar.of_card h2) blk (Prescribed.thickDirection
            (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk)).card) :
    Nonempty (TypeChangeLink m wd) := by
  rcases link_or_crossPair m wd h2 with h | ⟨blk, g, g', hsrc, hsplit, -, -, -, -⟩
  · exact h
  · have h4 := h3 blk hsrc
    have h5 := hsplit (Prescribed.thickDirection
      (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk)
    omega

/-- **The valency-two branch of the walk's `link` binder**, in the shape
`NonTrivalentValencyFourDispatcher.link_of_valency_three_two` asks for. -/
def typeChangeLink_of_valency_two
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (hCross : CrossPairLink m wd h2) : TypeChangeLink m wd :=
  (typeChangeLink_two m wd h2 hCross).some

/-- **The link at a same-direction pair over the thick direction, with no further
hypothesis.**  If the two survivors of the wall datum whose incoming rows are the rows of
the two occurrences the move brings together both lie over the thick target direction,
then the Base II merge realises the move, with no hypothesis about the candidate, no
no-return hypothesis and no incoming sub-case dispatch.  (A pair over the *thin*
direction is handled inside `link_or_crossPair` by re-reading the move from the other
end.) -/
theorem typeChangeLink_two_of_thick_pair
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (hsrc : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne)
      (TwoStar.of_card h2) blk)
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (hg : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ blk))
    (hg' : Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
      (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
        ⟨wd.a, wd.hab⟩ blk))
    (hne : g ≠ g')
    (hgT : (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) =
      Prescribed.thickEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk)
    (hgT' : (g'.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) =
      Prescribed.thickEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk)
    (hrow : survRow m wd g = rowT m wd) (hrow' : survRow m wd g' = rowR m wd) :
    Nonempty (TypeChangeLink m wd) := by
  classical
  have hNd := NonTrivalentValencyTwoRows.nonDanglingValency_anchor hsrc
  have hOrd := NonTrivalentValencyTwoRowEquiv.ordinaryTrivalent_of_wall_metric wd.cover
    wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) (TwoStar.of_card h2) wd.coordinates
    (label m.base) wd.hRows wd.hZeroCoord blk hNd
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) (TwoStar.of_card h2) wd.coordinates
      wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  exact nonempty_typeChangeLink_of_thick_rows m wd hsrc hOrd labelling₀ hRowVal hMatrixWall
    g g' hg hg' hne hgT hgT' hrow hrow'

/-- **Relative non-vacuity of (H-cross).**  At a `3 + 1` wall the hypothesis holds, its
`2 + 2` clause being unsatisfiable there; so the shape is not self-contradictory and what
the dispatcher leaves open really is confined to Configuration A. -/
theorem crossPairLink_of_three_thick
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (h3 : ∀ blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩,
      TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk →
        3 ≤ (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (TwoStar.of_card h2) blk (Prescribed.thickDirection
            (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk)).card) :
    CrossPairLink m wd h2 := by
  intro blk g g' hsrc hsplit _ _ _ _
  have h4 := h3 blk hsrc
  have h5 := hsplit (Prescribed.thickDirection
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk)
  omega

/-- The hypothesis is also implied by the conclusion, so it adds nothing beyond the link
itself at a wall where the link is already known. -/
theorem crossPairLink_of_link
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (h : Nonempty (TypeChangeLink m wd)) : CrossPairLink m wd h2 :=
  fun _ _ _ _ _ _ _ _ _ ↦ h

/-- **(H-BaseI) in the dispatcher's shape**: the cross pairing the move names has equal
dilation indices, so the numerical condition of Part II, Section 5.4, holds and the wall
carries a Base I member (`NonTrivalentValencyTwoBaseOneStarCount`). -/
def BaseOneCrossLink
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) : Prop :=
  ∀ (blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)),
    TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk →
      (∀ direction : Fin 2, (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (TwoStar.of_card h2) blk direction).card = 2) →
        Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ blk) →
          Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
              (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
                ⟨wd.a, wd.hab⟩ blk) →
            (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) ≠ g'.1.1.1 →
              ((survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
                (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd)) →
                (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 =
                    (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1 →
                  Nonempty (TypeChangeLink m wd)

/-- **(H-split) in the dispatcher's shape**: the cross pairing the move names has unequal
dilation indices, so that numerical condition fails and the wall carries a
Configuration A *split* member instead (`NonTrivalentValencyTwoSplitExit`, in its mirror
form when the index of the second member is the larger one).  The closing count of the
valency-two analysis in Part II, Section 5.4, is the statement that exactly one of the two
families realises each cross pairing. -/
def SplitCrossLink
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2) : Prop :=
  ∀ (blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
    (g g' : NonDanglingEdge (contractDatum wd.cover wd.hc wd.hab wd.hOne)),
    TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk →
      (∀ direction : Fin 2, (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (TwoStar.of_card h2) blk direction).card = 2) →
        Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g.1
            (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
              ⟨wd.a, wd.hab⟩ blk) →
          Incident (contractDatum wd.cover wd.hc wd.hab wd.hOne) g'.1
              (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne)
                ⟨wd.a, wd.hab⟩ blk) →
            (g.1.1.1 : (contract wd.coverTarget wd.hab wd.hOne).edges) ≠ g'.1.1.1 →
              ((survRow m wd g = rowT m wd ∧ survRow m wd g' = rowR m wd) ∨
                (survRow m wd g = rowR m wd ∧ survRow m wd g' = rowT m wd)) →
                (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 ≠
                    (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1 →
                  Nonempty (TypeChangeLink m wd)

/-- **(H-cross) splits along the index dichotomy of Part II, Section 5.4** (the Base I
index equalities, and the subcases where they fail). -/
theorem crossPairLink_of_index_dichotomy
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (hBaseOne : BaseOneCrossLink m wd h2) (hSplit : SplitCrossLink m wd h2) :
    CrossPairLink m wd h2 := by
  classical
  intro blk g g' hsrc hsplit hg hg' hne hrows
  by_cases hk : (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g.1 =
      (contractDatum wd.cover wd.hc wd.hab wd.hOne).sourceEdgeIndex g'.1
  · exact hBaseOne blk g g' hsrc hsplit hg hg' hne hrows hk
  · exact hSplit blk g g' hsrc hsplit hg hg' hne hrows hk

/-- Relative non-vacuity of the Base I half: at a `3 + 1` wall it holds, its `2 + 2`
clause being unsatisfiable there. -/
theorem baseOneCrossLink_of_three_thick
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (h3 : ∀ blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩,
      TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk →
        3 ≤ (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (TwoStar.of_card h2) blk (Prescribed.thickDirection
            (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk)).card) :
    BaseOneCrossLink m wd h2 := by
  intro blk g g' hsrc hsplit _ _ _ _ _
  have h4 := h3 blk hsrc
  have h5 := hsplit (Prescribed.thickDirection
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk)
  omega

/-- Relative non-vacuity of the split half, for the same reason. -/
theorem splitCrossLink_of_three_thick
    (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
      ⟨wd.a, wd.hab⟩).card = 2)
    (h3 : ∀ blk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩,
      TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk →
        3 ≤ (directionSurvivors (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (TwoStar.of_card h2) blk (Prescribed.thickDirection
            (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk)).card) :
    SplitCrossLink m wd h2 := by
  intro blk g g' hsrc hsplit _ _ _ _ _
  have h4 := h3 blk hsrc
  have h5 := hsplit (Prescribed.thickDirection
    (contractDatum wd.cover wd.hc wd.hab wd.hOne) (TwoStar.of_card h2) blk)
  omega

end Headline

/-! ## 10.  The walk's `link` binder with the valency-two branch discharged -/

section Dispatch

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **The `link` binder of `OuterWalk.coneEntry_of_reaches` with the four-valent branch
discharged by `NonTrivalentValencyFourDispatcher` and the two-valent branch discharged
here modulo the cross-pair hypothesis.**  What remains of `link` is the valency-three
exit and, at a `2 + 2`
Configuration A wall, the cross pair -- Base I when the two index equalities hold
(`NonTrivalentValencyTwoBaseOneStarCount`), the Configuration A split member otherwise
(`NonTrivalentValencyTwoSplitExit`). -/
def link_of_valency_three {G : CubicDartGraph D V}
    (h3 : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival),
        (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 3 → TypeChangeLink m wd)
    (hCross : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival)
        (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 2), CrossPairLink m wd h2) :
    ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival), TypeChangeLink m wd :=
  NonTrivalentValencyFourDispatcher.link_of_valency_three_two h3
    (fun K hK m arrival wd h2 ↦ typeChangeLink_of_valency_two m wd h2 (hCross K hK m arrival wd h2))

/-- **The `link` binder with the valency-two branch reduced to the two named families.**
`link_of_valency_three` with `CrossPairLink` split along the index dichotomy of Part II,
Section 5.4: the Base I half when the two cross-paired survivors have equal dilation
indices, the Configuration A split half when they do not. -/
def link_of_valency_three_of_dichotomy {G : CubicDartGraph D V}
    (h3 : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival),
        (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 3 → TypeChangeLink m wd)
    (hBaseOne : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival)
        (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 2), BaseOneCrossLink m wd h2)
    (hSplit : ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival)
        (h2 : (GluingDatum.incidentEdges (target := contract wd.coverTarget wd.hab wd.hOne)
          ⟨wd.a, wd.hab⟩).card = 2), SplitCrossLink m wd h2) :
    ∀ K : CubicDartGraph D V, CubicDartGraph.Reaches G K →
      ∀ (m : K.MoveData) (arrival : FacetArrival degree K label (label m.base))
        (wd : WallData arrival), TypeChangeLink m wd :=
  link_of_valency_three h3 (fun K hK m arrival wd h2 ↦
    crossPairLink_of_index_dichotomy m wd h2 (hBaseOne K hK m arrival wd h2)
      (hSplit K hK m arrival wd h2))

end Dispatch

end

end DraismaVargas.LocalCases.NonTrivalentValencyTwoDispatcher
