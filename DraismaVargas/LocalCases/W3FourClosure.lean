module

public import DraismaVargas.LocalCases.W3FourDisjointness

@[expose] public section

/-!
# Figure 28's Position I and Position II.b members, on branch-swapped wall data

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t2-(a=k₄)}`, its Positions
(I, II.a and II.b, set up in case `{w3-r1-nd3-t2}`), Figure 28 and
Equation (2).  Two reading conventions are used.  Part I works with
isomorphism classes of gluing data and does not say on which representative a
member's Position is read; here each member is realized on its own
branch-swapped representative.  And the individual regrown columns `c⁽ᵠ⁾` are
read off the boxes of Figure 28 rather than off the grouping of terms in the
displayed equation.

`W3FourSourceCandidates` builds Figure 28's two Position II.a members `M⁽³⁾`
and `M⁽⁴⁾` on the incoming datum, and shows that Position I and Position II.b
demand opposite things of the two smaller classes `e₂`, `e₃` of one fixed sheet
labelling (`exists_sheet_outside_iff_not_disjoint`).  `W3FourDisjointness`
shows that `Disjoint e₂ e₃` is a *gauge*: the branch-swap of Draisma--Vargas
Part I (§3.2), with its per-element notion of isomorphism of gluing data,
moves `e₃` while fixing `A₀`, `e₂` and `e₄`, and `𝒞*(M₀)` is a set of
isomorphism **classes** (§6.1).  This module builds the other two members on
the two branch-swapped representatives that machinery supplies.

## What is proved here

* `splitAlong` -- the two-block split of one wall block along a class, with the
  block, cardinality and refinement lemmas Position I needs.  Neither of
  Position I's two new-edge classes is cut out by a single target direction, so
  this partition has to be built rather than read off a `data.edgePartition`.
* `FourStarGeometry` -- the wall-local data of the case (three surviving
  directions, the two index identities `k₂ + k₃ = |A₀|` and `k₄ = |A₀|`, the
  dangling-singleton structure on `A₀`, and the `r = 0` census elsewhere),
  `ofGrowProfile` deriving it from an actual `ThirdEquation.W3SourceInput` plus
  `W3R1SourceProfile.Nd3Profile`, and `FourStarGeometry.swap` transporting all
  of it across `W3FourDisjointness.branchSwapOfPerm`.
* `FourStarGeometry.reversedCandidate` -- the shape both remaining members
  share: the whole block `A₀` at the divalent endpoint beside `t₄`, one
  refinement of `A₀` on the new edge *and* at the trivalent endpoint beside
  `t₂` and `t₃`.  This is the `LocalResolution.reverse` of
  `ResolutionCoarseFine.fineResolution`, the same distinction
  `W3Nd3SourceCandidates` records for Figure 30's `M⁽²⁾`.
* `PositionOne.candidate` -- Figure 28's `M⁽¹⁾`, with `candidate_valid`,
  `candidate_sourceGenus` and the displayed indices `|e'| = k₂`, `|e''| = k₃`.
* `PositionTwo.candidate` -- Figure 28's `M⁽²⁾`, with the same receipts and the
  displayed index `|e'| = k₄ - 1 = k₂ + k₃ - 1`.
* `exists_member_one`, `exists_member_two` -- both members realized on
  branch-swapped copies of **one** wall datum, each swap carrying a
  `W3FourDisjointness.BranchGauge`, and each displayed index equal to the
  *original* datum's index.
* `equationTwoFamily` and `exists_equationTwo_family` -- Equation (2) as a
  `BalancedGlobal.Family 4` over the incoming datum, with weights
  `1, k₂+k₃-1, k₂+1, k₃+1`; `rebase` is the one step that carries the two
  swapped members back.
* `equationTwo_residuals` -- the independent check that all four members are
  needed: dropping `M⁽¹⁾` leaves `σ₀(J₀,2) + σ₀(J₀,3) − σ₀(J₀,4)`, dropping
  `M⁽²⁾` leaves `σ₀(J₀,4)`, dropping `M⁽³⁾` leaves `−σ₀(J₀,2)` and dropping
  `M⁽⁴⁾` leaves `−σ₀(J₀,3)`.
* `GaugeFamily` and `GaugeFamily.exists_valid_positive_exit_with_pencil` -- the
  certified exit for a family whose members sit over different but
  gauge-equivalent data, which is what Figure 28 forces and
  `BalancedGlobal.PresentedFamily` does not allow; `equationTwoGaugeFamily`
  assembles Figure 28 into one, given length-matrix presentations.

## What is not proved here

* **The limit-matrix half**: no length-matrix presentation of any of the four
  members is constructed here, so Figure 28's determinants enter
  `equationTwoFamily` and `equationTwoGaugeFamily` as the hypothesis `hDet`
  rather than as a computation.  The same holds for the common off-wall columns
  (`hAgree`).  `W3FourStableGraph` and `W3FourLimitRows` supply both.
* **The stable-graph half**: no `StableGraphIncidence.Equivalence` between the
  incoming cover and any member is built here (see `W3FourStableIncidence`).
* **The incoming member identification** and the original-coordinate exit
  (`W3FourIncomingMatching`, `W3FourArbitraryExit`).
* **A transported `W3SourceInput`** on a branch-swapped copy.  `BranchGauge`
  covers every field of `ThirdEquation.W3SourceInput` except
  `nonDangling_valency`, so this module states the two members' input as
  `FourStarGeometry`, which *is* transported, and never claims the swapped
  datum is again a `W3SourceInput`.
* **The three branch flags.**  That the moved component contains `t₃` and
  neither `t₂` nor `t₄` is carried explicitly, exactly as `W3FourDisjointness`
  leaves it.  It holds on any target tree with `root` the far endpoint of `t₃`
  and `TargetBranchRegion.vertexMoved` decides it on any concrete target, but
  `W3SourceInput` carries no target acyclicity, so it is not derived.

No FourStar theorem is applied to this ThreeStar case.

## Why the hypotheses can hold at once

`FourStarGeometry` is inhabited on every literal datum of the case:
`ofGrowProfile` produces one from an arbitrary `W3SourceInput` and an arbitrary
`W3FourSourceCandidates.GrowProfile`, and the latter is produced from any
`Nd3Profile` plus the two arithmetic conditions of
`W3IncomingClassification.Classification.four` by the total functions
`growProfileFirst` / `growProfileSecond`.  `PositionOne`'s extra field
(`Disjoint e₂ e₃`) and `PositionTwo`'s extra fields (a sheet of `A₀` outside
both) are *opposite* conditions, and that is the point: `exists_member_one` and
`exists_member_two` produce each of them on its own branch-swapped
representative of the same datum, so neither structure is empty and no single
datum is asked to satisfy both.  `equationTwo_residuals` and
`equationTwoFamily` need only `1 ≤ k₂`, `1 ≤ k₃` and the limit's own three
relations, which hold together (for instance with `k₂ = k₃ = 1` and every `c`
and `σ₀` zero).

## Which datum this is about

`ThirdEquation.W3SourceInput` carries `equation_c : data.targetExcess wall = 1`,
so everything here lives on the wall/limit side of the bridge recorded in
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`, exactly as
`W3FourSourceCandidates` does.  `GaugeFamily` and `equationTwoGaugeFamily` speak
about length-matrix presentations of the **outgoing** members, which is the
other side; no single object is asked to be both.
-/
namespace DraismaVargas.LocalCases.W3FourClosure

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile ResolutionCoarseFine
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary M11SourceGenus
open W3Nd2SourceCandidates (OrientedStar rightOf wallEdgesAssigned_false
  wallEdgesAssigned_true external_count_eq)
open W3FourDisjointness
open W3FourSourceCandidates (blockCountWithin_of_singletons_off_block)

variable {d : ℕ}

/-! ## Splitting one wall block along a class

Position I of Figure 28 needs the partition of the distinguished wall block
`A₀` into the two smaller surviving classes `e₂` and `e₃`.  Neither is cut out
by a single target direction -- that is the whole point of the case -- so the
partition is built here, from the class `e₂` and the block `A₀`, and is the
wall partition away from `A₀`.  It is a two-block refinement of `A₀` exactly
when `e₂` is a proper nonempty subset, which the case's index identity
`k₂ + k₃ = |A₀|` with `k₃ > 0` supplies. -/

section SplitAlong

def splitAlongRepr (coarse fine : SheetPartition d) (pivot alt i : Fin d) :
    Fin d :=
  if coarse.Rel pivot i then (if fine.Rel pivot i then pivot else alt)
  else coarse.repr i

/-- Split the `coarse` block through `pivot` into the `fine` class through
`pivot` and the rest of that block, represented by `alt`.  Every other block
of `coarse` is left literally unchanged. -/
def splitAlong (coarse fine : SheetPartition d) (pivot alt : Fin d)
    (hAlt : coarse.Rel pivot alt) (hSep : ¬fine.Rel pivot alt) :
    SheetPartition d where
  repr := splitAlongRepr coarse fine pivot alt
  repr_idem := by
    intro i
    unfold splitAlongRepr
    by_cases hi : coarse.Rel pivot i
    · rw [ite_eq_left hi]
      by_cases hf : fine.Rel pivot i
      · rw [ite_eq_left hf, ite_eq_left (show coarse.Rel pivot pivot from rfl),
          ite_eq_left (show fine.Rel pivot pivot from rfl)]
      · rw [ite_eq_right hf, ite_eq_left hAlt, ite_eq_right hSep]
    · rw [ite_eq_right hi]
      have hRepr : ¬coarse.Rel pivot (coarse.repr i) := fun h ↦
        hi (h.trans (coarse.rel_repr_left i))
      rw [ite_eq_right hRepr, coarse.repr_idem i]

variable {coarse fine : SheetPartition d} {pivot alt : Fin d}

theorem splitAlong_repr_eq (hAlt : coarse.Rel pivot alt)
    (hSep : ¬fine.Rel pivot alt) (i : Fin d) :
    (splitAlong coarse fine pivot alt hAlt hSep).repr i =
      if coarse.Rel pivot i then (if fine.Rel pivot i then pivot else alt)
      else coarse.repr i := rfl

/-- The two representatives of the split block are distinct. -/
theorem splitAlong_pivot_ne_alt (hSep : ¬fine.Rel pivot alt) : pivot ≠ alt := by
  rintro rfl
  exact hSep rfl

theorem splitAlong_repr_pivot (hAlt : coarse.Rel pivot alt)
    (hSep : ¬fine.Rel pivot alt) :
    (splitAlong coarse fine pivot alt hAlt hSep).repr pivot = pivot := by
  rw [splitAlong_repr_eq, ite_eq_left (show coarse.Rel pivot pivot from rfl),
    ite_eq_left (show fine.Rel pivot pivot from rfl)]

theorem splitAlong_repr_alt (hAlt : coarse.Rel pivot alt)
    (hSep : ¬fine.Rel pivot alt) :
    (splitAlong coarse fine pivot alt hAlt hSep).repr alt = alt := by
  rw [splitAlong_repr_eq, ite_eq_left hAlt, ite_eq_right hSep]

/-- Outside the split block the canonical representative is neither of the two
new ones. -/
private theorem repr_ne_of_not_rel (hAlt : coarse.Rel pivot alt) {i : Fin d}
    (hi : ¬coarse.Rel pivot i) :
    coarse.repr i ≠ pivot ∧ coarse.repr i ≠ alt := by
  have hSelf : coarse.Rel (coarse.repr i) i := coarse.rel_repr_left i
  refine ⟨fun hEq ↦ hi (hEq ▸ hSelf), fun hEq ↦ hi ?_⟩
  exact hAlt.trans (hEq ▸ hSelf)

/-- The split partition refines the original one. -/
theorem splitAlong_refines (hAlt : coarse.Rel pivot alt)
    (hSep : ¬fine.Rel pivot alt) :
    (splitAlong coarse fine pivot alt hAlt hSep).Refines coarse := by
  intro i j hij
  rw [SheetPartition.rel_iff, splitAlong_repr_eq, splitAlong_repr_eq] at hij
  by_cases hi : coarse.Rel pivot i
  · rw [ite_eq_left hi] at hij
    by_cases hj : coarse.Rel pivot j
    · exact hi.symm.trans hj
    · rw [ite_eq_right hj] at hij
      obtain ⟨hPivot, hAltNe⟩ := repr_ne_of_not_rel hAlt hj
      split_ifs at hij
      · exact absurd hij.symm hPivot
      · exact absurd hij.symm hAltNe
  · rw [ite_eq_right hi] at hij
    obtain ⟨hPivot, hAltNe⟩ := repr_ne_of_not_rel hAlt hi
    by_cases hj : coarse.Rel pivot j
    · rw [ite_eq_left hj] at hij
      split_ifs at hij
      · exact absurd hij hPivot
      · exact absurd hij hAltNe
    · rw [ite_eq_right hj] at hij
      exact hij

/-- Any partition refining `coarse` which never separates the `fine` class
through `pivot` from its complement inside the split block refines the split
partition. -/
theorem refines_splitAlong (hAlt : coarse.Rel pivot alt)
    (hSep : ¬fine.Rel pivot alt) (other : SheetPartition d)
    (hOther : other.Refines coarse)
    (hCompat : ∀ i j, coarse.Rel pivot i → other.Rel i j →
      (fine.Rel pivot i ↔ fine.Rel pivot j)) :
    other.Refines (splitAlong coarse fine pivot alt hAlt hSep) := by
  intro i j hij
  have hCoarse := hOther.rel hij
  rw [SheetPartition.rel_iff, splitAlong_repr_eq, splitAlong_repr_eq]
  by_cases hi : coarse.Rel pivot i
  · have hj : coarse.Rel pivot j := hi.trans hCoarse
    rw [ite_eq_left hi, ite_eq_left hj]
    by_cases hf : fine.Rel pivot i
    · rw [ite_eq_left hf, ite_eq_left ((hCompat i j hi hij).mp hf)]
    · rw [ite_eq_right hf, ite_eq_right (fun h ↦ hf ((hCompat i j hi hij).mpr h))]
  · have hj : ¬coarse.Rel pivot j := fun h ↦ hi (h.trans hCoarse.symm)
    rw [ite_eq_right hi, ite_eq_right hj]
    exact hCoarse

/-- The `fine` class through `pivot` is one block of the split partition. -/
theorem splitAlong_block_pivot (hAlt : coarse.Rel pivot alt)
    (hSep : ¬fine.Rel pivot alt) (hFine : fine.Refines coarse) :
    (splitAlong coarse fine pivot alt hAlt hSep).block pivot =
      fine.block pivot := by
  ext j
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff,
    SheetPartition.rel_iff, splitAlong_repr_pivot hAlt hSep, splitAlong_repr_eq]
  by_cases hj : coarse.Rel pivot j
  · rw [ite_eq_left hj]
    by_cases hf : fine.Rel pivot j
    · rw [ite_eq_left hf]
      exact iff_of_true rfl hf
    · rw [ite_eq_right hf]
      exact iff_of_false (splitAlong_pivot_ne_alt hSep) hf
  · rw [ite_eq_right hj]
    obtain ⟨hPivot, _⟩ := repr_ne_of_not_rel hAlt hj
    exact iff_of_false (fun h ↦ hPivot h.symm) (fun h ↦ hj (hFine.rel h))

/-- Its complement inside the split block is the other. -/
theorem splitAlong_block_alt (hAlt : coarse.Rel pivot alt)
    (hSep : ¬fine.Rel pivot alt) :
    (splitAlong coarse fine pivot alt hAlt hSep).block alt =
      coarse.block pivot \ fine.block pivot := by
  ext j
  rw [SheetPartition.mem_block_iff, Finset.mem_sdiff, SheetPartition.mem_block_iff,
    SheetPartition.mem_block_iff, SheetPartition.rel_iff,
    splitAlong_repr_alt hAlt hSep, splitAlong_repr_eq]
  by_cases hj : coarse.Rel pivot j
  · rw [ite_eq_left hj]
    by_cases hf : fine.Rel pivot j
    · rw [ite_eq_left hf]
      exact iff_of_false (fun h ↦ splitAlong_pivot_ne_alt hSep h.symm)
        (fun h ↦ h.2 hf)
    · rw [ite_eq_right hf]
      exact iff_of_true rfl ⟨hj, hf⟩
  · rw [ite_eq_right hj]
    obtain ⟨_, hAltNe⟩ := repr_ne_of_not_rel hAlt hj
    exact iff_of_false (fun h ↦ hAltNe h.symm) (fun h ↦ hj h.1)

theorem splitAlong_blockCard_pivot (hAlt : coarse.Rel pivot alt)
    (hSep : ¬fine.Rel pivot alt) (hFine : fine.Refines coarse) :
    (splitAlong coarse fine pivot alt hAlt hSep).blockCard pivot =
      fine.blockCard pivot := by
  unfold SheetPartition.blockCard
  rw [splitAlong_block_pivot hAlt hSep hFine]

theorem splitAlong_blockCard_alt (hAlt : coarse.Rel pivot alt)
    (hSep : ¬fine.Rel pivot alt) (hFine : fine.Refines coarse) :
    (splitAlong coarse fine pivot alt hAlt hSep).blockCard alt +
        fine.blockCard pivot = coarse.blockCard pivot := by
  unfold SheetPartition.blockCard
  rw [splitAlong_block_alt hAlt hSep]
  refine Finset.card_sdiff_add_card_eq_card ?_
  intro sheet hSheet
  exact (coarse.mem_block_iff pivot sheet).mpr
    (hFine.rel ((fine.mem_block_iff pivot sheet).mp hSheet))

end SplitAlong


/-! ## The local geometry of Figure 28's limit `M₀`

Everything both members need from the wall datum, packaged so that it can be
carried across a branch swap.  Each field is a literal statement
about the wall partition and the three incident edge partitions; nothing here
mentions `ThirdEquation.W3SourceInput`, whose `nonDangling_valency` field is
the one piece `W3FourDisjointness.BranchGauge` does not transport. -/

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- The wall-local data of case `{w3-r1-nd3-t2-(a=k₄)}`: three distinct
surviving directions `t₂`, `t₃`, `t₄` at a trivalent wall, with classes
`e₂`, `e₃`, `e₄` inside one wall block `A₀`, the index identities
`k₂ + k₃ = |A₀|` and `k₄ = |A₀|`, the dangling-singleton structure of the two
smaller directions on `A₀`, and the `r = 0` Riemann--Hurwitz census on every
other wall block. -/
structure FourStarGeometry (data : GluingDatum target degree)
    (wall : target.V) where
  /-- `t₂`: the direction of the first smaller survivor `e₂`. -/
  growTarget : target.edges
  /-- `t₃`: the direction of the second smaller survivor `e₃`. -/
  otherTarget : target.edges
  /-- `t₄`: the direction of the full-degree survivor `e₄`. -/
  largestTarget : target.edges
  grow_ne_other : growTarget ≠ otherTarget
  grow_ne_largest : growTarget ≠ largestTarget
  other_ne_largest : otherTarget ≠ largestTarget
  /-- The wall star is exactly those three directions. -/
  incidentEdges_eq : GluingDatum.incidentEdges wall =
    {growTarget, otherTarget, largestTarget}
  /-- A sheet of `e₂`. -/
  growAnchor : Fin degree
  /-- A sheet of `e₃`. -/
  otherAnchor : Fin degree
  /-- A sheet of `e₄`. -/
  largestAnchor : Fin degree
  other_wall_rel : (data.vertexPartition wall).Rel growAnchor otherAnchor
  largest_wall_rel : (data.vertexPartition wall).Rel growAnchor largestAnchor
  /-- Off `e₂`, the direction `t₂` is singleton-refined on `A₀`. -/
  grow_singletons : ∀ sheet, (data.vertexPartition wall).Rel growAnchor sheet →
    ¬(data.edgePartition growTarget).Rel growAnchor sheet →
    (data.edgePartition growTarget).blockCard sheet = 1
  /-- Off `e₃`, the direction `t₃` is singleton-refined on `A₀`. -/
  other_singletons : ∀ sheet, (data.vertexPartition wall).Rel growAnchor sheet →
    ¬(data.edgePartition otherTarget).Rel otherAnchor sheet →
    (data.edgePartition otherTarget).blockCard sheet = 1
  /-- `k₂ + k₃ = |A₀|`, the defining identity of the case. -/
  index_sum : (data.edgePartition growTarget).blockCard growAnchor +
    (data.edgePartition otherTarget).blockCard otherAnchor =
    (data.vertexPartition wall).blockCard growAnchor
  /-- `k₄ = |A₀|`, which is what selects `(a = k₄)`. -/
  largest_index : (data.edgePartition largestTarget).blockCard largestAnchor =
    (data.vertexPartition wall).blockCard growAnchor
  /-- The unramified Riemann--Hurwitz census on every other wall block. -/
  background : ∀ sheet, ¬(data.vertexPartition wall).Rel growAnchor sheet →
    (data.edgePartition growTarget).blockCountWithin
        (data.vertexPartition wall) sheet +
      (data.edgePartition otherTarget).blockCountWithin
        (data.vertexPartition wall) sheet +
      (data.edgePartition largestTarget).blockCountWithin
        (data.vertexPartition wall) sheet =
    (data.vertexPartition wall).blockCard sheet + 2

namespace FourStarGeometry

variable (geometry : FourStarGeometry data wall)

theorem growTarget_mem : geometry.growTarget ∈ GluingDatum.incidentEdges wall := by
  rw [geometry.incidentEdges_eq]; simp

theorem otherTarget_mem : geometry.otherTarget ∈ GluingDatum.incidentEdges wall := by
  rw [geometry.incidentEdges_eq]; simp

theorem largestTarget_mem :
    geometry.largestTarget ∈ GluingDatum.incidentEdges wall := by
  rw [geometry.incidentEdges_eq]; simp

theorem grow_refines :
    (data.edgePartition geometry.growTarget).Refines (data.vertexPartition wall) :=
  refines_of_mem_incidentEdges data geometry.growTarget_mem

theorem other_refines :
    (data.edgePartition geometry.otherTarget).Refines (data.vertexPartition wall) :=
  refines_of_mem_incidentEdges data geometry.otherTarget_mem

theorem largest_refines :
    (data.edgePartition geometry.largestTarget).Refines
      (data.vertexPartition wall) :=
  refines_of_mem_incidentEdges data geometry.largestTarget_mem

/-- The second smaller class is a proper subset of `A₀`: its complement has
`k₂ > 0` sheets. -/
theorem other_blockCard_lt :
    (data.edgePartition geometry.otherTarget).blockCard geometry.otherAnchor <
      (data.vertexPartition wall).blockCard geometry.growAnchor := by
  have hPos := (data.edgePartition geometry.growTarget).blockCard_pos
    geometry.growAnchor
  have hSum := geometry.index_sum
  omega

/-- The first smaller class is a proper subset of `A₀`. -/
theorem grow_blockCard_lt :
    (data.edgePartition geometry.growTarget).blockCard geometry.growAnchor <
      (data.vertexPartition wall).blockCard geometry.growAnchor := by
  have hPos := (data.edgePartition geometry.otherTarget).blockCard_pos
    geometry.otherAnchor
  have hSum := geometry.index_sum
  omega

end FourStarGeometry


/-! ## The literal `w3Four` geometry of an actual source input -/

section OfSource

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

open W3FourSourceCandidates

/-- Figure 28's limit geometry, read off the source's own `GrowProfile`: no
numerical diagram is supplied, every field is derived from
`ThirdEquation.W3SourceInput` and `W3R1SourceProfile.Nd3Profile`. -/
noncomputable def ofGrowProfile (grown : GrowProfile input) :
    FourStarGeometry data wall where
  growTarget := grown.growTarget
  otherTarget := grown.otherTarget
  largestTarget := grown.largestTarget
  grow_ne_other := grown.grow_target_ne_other
  grow_ne_largest := grown.grow_target_ne_largest
  other_ne_largest := grown.other_target_ne_largest
  incidentEdges_eq := grown.incidentEdges_eq
  growAnchor := grown.growAnchor
  otherAnchor := grown.otherAnchor
  largestAnchor := grown.largestAnchor
  other_wall_rel := grown.growAnchor_wall_rel.symm.trans grown.otherAnchor_wall_rel
  largest_wall_rel :=
    grown.growAnchor_wall_rel.symm.trans grown.largestAnchor_wall_rel
  grow_singletons := fun sheet hSheet hNe ↦
    grow_blockCard_eq_one grown sheet (grown.growAnchor_wall_rel.trans hSheet) hNe
  other_singletons := fun sheet hSheet hNe ↦
    other_blockCard_eq_one grown sheet (grown.growAnchor_wall_rel.trans hSheet) hNe
  index_sum := by
    have hSum := grown.index_sum
    have hCard : (data.vertexPartition wall).blockCard input.distinguishedBlock.1 =
        (data.vertexPartition wall).blockCard grown.growAnchor :=
      SheetPartition.blockCard_congr _ grown.growAnchor_wall_rel
    rw [← hCard]
    exact hSum
  largest_index := by
    have hCard : (data.vertexPartition wall).blockCard input.distinguishedBlock.1 =
        (data.vertexPartition wall).blockCard grown.growAnchor :=
      SheetPartition.blockCard_congr _ grown.growAnchor_wall_rel
    rw [← hCard]
    exact grown.largest_index
  background := by
    intro sheet hNot
    have hSheetOther : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet := fun h ↦ hNot
      (grown.growAnchor_wall_rel.symm.trans h)
    have hBlockNe : (data.vertexPartition wall).toBlock sheet ≠
        input.distinguishedBlock := by
      intro hEq
      apply hSheetOther
      have hValue := congrArg Subtype.val hEq
      change (data.vertexPartition wall).repr sheet =
        input.distinguishedBlock.1 at hValue
      change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
        (data.vertexPartition wall).repr sheet
      rw [input.distinguishedBlock.2, hValue]
    have hZero := input.localRamification_eq_zero_of_ne hBlockNe
    have hTotal := external_count_eq (data := data) star grown.orientation sheet
    rw [hZero] at hTotal
    have hTotalNat :
        (data.edgePartition grown.growTarget).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition grown.otherTarget).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition grown.largestTarget).blockCountWithin
              (data.vertexPartition wall) sheet =
          0 + 2 + (data.vertexPartition wall).blockCard sheet := by
      exact_mod_cast hTotal
    omega

/-- The transferred sheet changes Position II.a's fine partition but not the
underlying four-star geometry used by Positions I and II.b. -/
@[simp] theorem ofGrowProfile_withExtra (grown : GrowProfile input) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSep : ¬(data.edgePartition grown.growTarget).Rel grown.growAnchor sheet) :
    ofGrowProfile (grown.withExtra sheet hWall hSep) = ofGrowProfile grown := by
  cases grown
  rfl

end OfSource

/-! ## Transport across a branch swap

`W3FourDisjointness.BranchGauge` records what a branch swap leaves alone at the
level of the wall datum.  What the two members actually consume is
the geometry above, so this is the transport statement they need: on the branch
through `t₃`, with `t₂` and `t₄` outside it, the whole case geometry survives
with `e₃` replaced by its image and its index unchanged. -/

namespace FourStarGeometry

/-- The case geometry of Figure 28 transported along the branch swap of
Draisma--Vargas Part I (§3.2) by a block-preserving permutation, on a branch
containing `t₃` and avoiding `t₂` and `t₄`. The two "fixed" flags and the
"moved" flag are the hypotheses `W3FourDisjointness` leaves named rather than
derived: they hold on any target tree with `root` the far endpoint of `t₃`, and
`TargetBranchRegion.vertexMoved` makes them decidable on any concrete target. -/
noncomputable def swap (geometry : FourStarGeometry data wall)
    (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.growTarget = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.largestTarget = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.otherTarget = true) :
    FourStarGeometry
      (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall where
  growTarget := geometry.growTarget
  otherTarget := geometry.otherTarget
  largestTarget := geometry.largestTarget
  grow_ne_other := geometry.grow_ne_other
  grow_ne_largest := geometry.grow_ne_largest
  other_ne_largest := geometry.other_ne_largest
  incidentEdges_eq := geometry.incidentEdges_eq
  growAnchor := geometry.growAnchor
  otherAnchor := permutation geometry.otherAnchor
  largestAnchor := geometry.largestAnchor
  other_wall_rel := by
    rw [branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix]
    exact geometry.other_wall_rel.trans (hFix geometry.otherAnchor).symm
  largest_wall_rel := by
    rw [branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix]
    exact geometry.largest_wall_rel
  grow_singletons := by
    rw [branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix,
      branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot permutation hFix
        geometry.growTarget hGrowFixed]
    exact geometry.grow_singletons
  other_singletons := by
    rw [branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix,
      branchSwapOfPerm_edgePartition_of_moved data wall root hRoot permutation hFix
        geometry.otherTarget hOtherMoved]
    intro sheet hSheet hNe
    obtain ⟨source, rfl⟩ : ∃ source, sheet = permutation source :=
      ⟨permutation.symm sheet, by simp⟩
    rw [SheetPartition.relabel_blockCard]
    refine geometry.other_singletons source (hSheet.trans (hFix source)) ?_
    intro hRel
    exact hNe ((SheetPartition.relabel_rel_iff _ _ _ _).mpr hRel)
  index_sum := by
    rw [branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix,
      branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot permutation hFix
        geometry.growTarget hGrowFixed,
      branchSwapOfPerm_edgePartition_of_moved data wall root hRoot permutation hFix
        geometry.otherTarget hOtherMoved, SheetPartition.relabel_blockCard]
    exact geometry.index_sum
  largest_index := by
    rw [branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix,
      branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot permutation hFix
        geometry.largestTarget hLargestFixed]
    exact geometry.largest_index
  background := by
    intro sheet hNot
    rw [branchSwapOfPerm_blockCountWithin_wall data wall root hRoot permutation hFix,
      branchSwapOfPerm_blockCountWithin_wall data wall root hRoot permutation hFix,
      branchSwapOfPerm_blockCountWithin_wall data wall root hRoot permutation hFix,
      branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix]
    rw [branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation
      hFix] at hNot
    exact geometry.background sheet hNot

@[simp] theorem swap_growTarget (geometry : FourStarGeometry data wall)
    (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.growTarget = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.largestTarget = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.otherTarget = true) :
    (geometry.swap root hRoot permutation hFix hGrowFixed hLargestFixed
      hOtherMoved).growTarget = geometry.growTarget := rfl

@[simp] theorem swap_growAnchor (geometry : FourStarGeometry data wall)
    (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.growTarget = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.largestTarget = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.otherTarget = true) :
    (geometry.swap root hRoot permutation hFix hGrowFixed hLargestFixed
      hOtherMoved).growAnchor = geometry.growAnchor := rfl

@[simp] theorem swap_otherAnchor (geometry : FourStarGeometry data wall)
    (root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.growTarget = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.largestTarget = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.otherTarget = true) :
    (geometry.swap root hRoot permutation hFix hGrowFixed hLargestFixed
      hOtherMoved).otherAnchor = permutation geometry.otherAnchor := rfl


/-! ## The common shape of `M⁽¹⁾` and `M⁽²⁾`

Both Figure 28 members built here are oriented the same way: the whole wall
block `A₀` stays at the divalent endpoint `u` beside `t₄`, and one refinement
of `A₀` sits on the new edge `t₁` **and** at the trivalent endpoint `v`,
beside `t₂` and `t₃`.  They differ only in that refinement -- the two blocks
`e₂`, `e₃` for Position I, and `A₀` minus one sheet for Position II.b -- so the
assembly is carried out once here and instantiated twice below.

This is the **reverse** of `ResolutionCoarseFine.fineResolution`, which places
the refinement at the divalent endpoint; that is the same distinction
`W3Nd3SourceCandidates` records for Figure 30's `M⁽²⁾`. -/

/-- The orientation of the wall star used by both members: `t₄` alone at the
divalent endpoint, `t₂` and `t₃` at the trivalent endpoint. -/
noncomputable def orientation (geometry : FourStarGeometry data wall) :
    OrientedStar target wall geometry.largestTarget where
  rightFirst := geometry.growTarget
  rightSecond := geometry.otherTarget
  left_mem := geometry.largestTarget_mem
  rightFirst_ne_left := geometry.grow_ne_largest
  rightSecond_ne_left := geometry.other_ne_largest
  right_ne := geometry.grow_ne_other
  incidentEdges_eq := by
    rw [geometry.incidentEdges_eq]
    ext edge
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- Every unramified wall block is resolved with the `t₄` partition on the new
edge and at the divalent endpoint; the original `r = 0` census is exactly the
trivalent count there, so no background receipt is assumed. -/
noncomputable def wallBackground (geometry : FourStarGeometry data wall) :
    Background data wall geometry.growAnchor := by
  let orientation := geometry.orientation
  let fine := data.edgePartition geometry.largestTarget
  have hFine := geometry.largest_refines
  let localResolution : LocalResolution degree :=
    fineResolution (data.vertexPartition wall) fine hFine
  refine {
    right := rightOf geometry.largestTarget
    resolution := fun _ ↦ localResolution
    contracts := ?_
    exterior := ?_
    leftEdges := [geometry.largestTarget]
    rightEdges := [orientation.rightFirst, orientation.rightSecond]
    leftEdges_eq := ?_
    rightEdges_eq := ?_
    left_riemannHurwitz := ?_
    right_riemannHurwitz := ?_ }
  · intro _ _
    exact fineResolution_contracts _ fine hFine
  · intro edge hIncident _ _
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hEq : edge = geometry.largestTarget
    · subst edge
      change fine.Refines
        (if rightOf geometry.largestTarget geometry.largestTarget then
          localResolution.right else localResolution.left)
      simp only [rightOf, ne_eq, not_true_eq_false, decide_false,
        localResolution, fineResolution]
      exact SheetPartition.Refines.refl fine
    · have hRight : rightOf geometry.largestTarget edge = true := by
        simp [rightOf, hEq]
      rw [hRight, ite_eq_left rfl]
      change (data.edgePartition edge).Refines (data.vertexPartition wall)
      exact refines_of_mem_incidentEdges data hAt
  · rw [wallEdgesAssigned_false orientation]
    rfl
  · rw [wallEdgesAssigned_true orientation]
    rw [Finset.insert_val_of_notMem (by simpa using orientation.right_ne)]
    rfl
  · intro blockAnchor _ _
    exact fineResolution_left_riemannHurwitzAtBlock
      (data.vertexPartition wall) fine
      (data.edgePartition geometry.largestTarget) hFine blockAnchor
  · intro blockAnchor _ hOther
    apply riemannHurwitzAtBlock_trivalent_of_counts
      (data.vertexPartition wall) (data.vertexPartition wall) fine
      (data.edgePartition orientation.rightFirst)
      (data.edgePartition orientation.rightSecond) blockAnchor
    intro sheet hSheet
    have hSheetOther : ¬(data.vertexPartition wall).Rel geometry.growAnchor sheet :=
      fun hRel ↦ hOther (hRel.trans hSheet.symm)
    have hTotal := geometry.background sheet hSheetOther
    change (data.edgePartition geometry.largestTarget).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition geometry.growTarget).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition geometry.otherTarget).blockCountWithin
          (data.vertexPartition wall) sheet ≥
      (data.vertexPartition wall).blockCard sheet + 2
    omega

/-- The common Figure 28 member built from one refinement of the distinguished
wall block.  `hCounts` is the trivalent Riemann--Hurwitz census, and is the
only thing Position I and Position II.b have to supply separately. -/
noncomputable def reversedCandidate (geometry : FourStarGeometry data wall)
    (fine : SheetPartition degree)
    (hFine : fine.Refines (data.vertexPartition wall))
    (hGrow : (data.edgePartition geometry.growTarget).Refines fine)
    (hOther : (data.edgePartition geometry.otherTarget).Refines fine)
    (hCounts : ∀ sheet, (data.vertexPartition wall).Rel geometry.growAnchor sheet →
      fine.blockCountWithin fine sheet +
          (data.edgePartition geometry.growTarget).blockCountWithin fine sheet +
          (data.edgePartition geometry.otherTarget).blockCountWithin fine sheet ≥
        fine.blockCard sheet + 2) :
    BalancedGlobal.Candidate target degree data wall := by
  let background := geometry.wallBackground
  let selected : LocalResolution degree :=
    (fineResolution (data.vertexPartition wall) fine hFine).reverse
  apply background.install selected
    (LocalResolution.reverse_contracts
      (fineResolution_contracts (data.vertexPartition wall) fine hFine))
  · intro edge hIncident
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hLargest : edge = geometry.largestTarget
    · subst edge
      simp only [background, FourStarGeometry.wallBackground, rightOf, ne_eq,
        not_true_eq_false, decide_false, selected, LocalResolution.reverse_left,
        fineResolution]
      exact refines_of_mem_incidentEdges data hAt
    · have hRight : rightOf geometry.largestTarget edge = true := by
        simp [rightOf, hLargest]
      simp only [background, FourStarGeometry.wallBackground, hRight, ite_true,
        selected, LocalResolution.reverse_right, fineResolution]
      have hCases : edge = geometry.growTarget ∨ edge = geometry.otherTarget := by
        rw [geometry.incidentEdges_eq] at hAt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hAt
        rcases hAt with hGrowEq | hOtherEq | hLargestEq
        · exact Or.inl hGrowEq
        · exact Or.inr hOtherEq
        · exact (hLargest hLargestEq).elim
      rcases hCases with rfl | rfl
      · exact hGrow
      · exact hOther
  · intro blockAnchor _ _
    change LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (data.vertexPartition wall)
      [fine, data.edgePartition geometry.largestTarget] blockAnchor
    exact riemannHurwitzAtBlock_divalent _ _ _ _ _
  · intro blockAnchor hAnchor _
    change LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      fine [fine, data.edgePartition geometry.growTarget,
        data.edgePartition geometry.otherTarget] blockAnchor
    apply riemannHurwitzAtBlock_trivalent_of_counts
    intro sheet hSheet
    exact hCounts sheet (hAnchor.trans hSheet)

variable (geometry : FourStarGeometry data wall) (fine : SheetPartition degree)
  (hFine : fine.Refines (data.vertexPartition wall))
  (hGrow : (data.edgePartition geometry.growTarget).Refines fine)
  (hOther : (data.edgePartition geometry.otherTarget).Refines fine)
  (hCounts : ∀ sheet, (data.vertexPartition wall).Rel geometry.growAnchor sheet →
    fine.blockCountWithin fine sheet +
        (data.edgePartition geometry.growTarget).blockCountWithin fine sheet +
        (data.edgePartition geometry.otherTarget).blockCountWithin fine sheet ≥
      fine.blockCard sheet + 2)

/-- Either member is valid whenever the datum it is built on is. -/
theorem reversedCandidate_valid (hValid : data.Valid) :
    (geometry.reversedCandidate fine hFine hGrow hOther hCounts).datum.Valid :=
  (geometry.reversedCandidate fine hFine hGrow hOther hCounts).datum_valid hValid

/-- Either member preserves the complete quotient-source genus: the selected
block and the background blocks are pasted stars in opposite orientations. -/
theorem reversedCandidate_sourceGenus :
    genus (geometry.reversedCandidate fine hFine hGrow hOther hCounts).datum.sourceGraph =
      genus data.sourceGraph := by
  apply candidate_sourceGenus_of_stars
  intro anchor
  have hResolution :
      (geometry.reversedCandidate fine hFine hGrow hOther hCounts).resolution anchor =
        LocalResolution.onBlock (data.vertexPartition wall) geometry.growAnchor
          ((fineResolution (data.vertexPartition wall) fine hFine).reverse)
          geometry.wallBackground.resolution anchor := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel geometry.growAnchor anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    exact Or.inr ⟨rfl, rfl⟩

/-- On the distinguished block the member is literally the reversed star. -/
theorem reversedCandidate_resolution_selected {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel geometry.growAnchor sheet) :
    (geometry.reversedCandidate fine hFine hGrow hOther hCounts).resolution sheet =
      (fineResolution (data.vertexPartition wall) fine hFine).reverse := by
  change LocalResolution.onBlock (data.vertexPartition wall) geometry.growAnchor
      ((fineResolution (data.vertexPartition wall) fine hFine).reverse)
      geometry.wallBackground.resolution sheet = _
  rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSheet]

/-- Over the distinguished wall block the new edge carries exactly the chosen
refinement, so its displayed class sizes are those of `fine`. -/
theorem reversedCandidate_newEdge {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel geometry.growAnchor sheet) :
    ((geometry.reversedCandidate fine hFine hGrow hOther hCounts).resolution
      sheet).newEdge = fine := by
  rw [reversedCandidate_resolution_selected geometry fine hFine hGrow hOther
    hCounts hSheet]
  rfl

end FourStarGeometry

/-! ## Figure 28's `M⁽¹⁾`: Position I

Position I (Part I, case `{w3-r1-nd3-t2}`) puts the `nd = 3` vertex `A⁽¹⁾` above the divalent
endpoint `u`, incident to `e₄`; since `|A⁽¹⁾| = |e₄| = |A₀|` it is the whole
wall block.  The new edge `t₁` carries exactly two classes `e'`, `e''` of sizes
`k₂`, `k₃`, and their other ends above the trivalent endpoint `v` are equal, as
subsets of `[d]`, to `e₂` and `e₃`.  So the trivalent endpoint's partition and
the new edge's partition are both the two-block split of `A₀` into `e₂` and its
complement, which is `e₃` exactly when `e₂` and `e₃` are disjoint. -/

/-- Figure 28's `M⁽¹⁾` data: the case geometry on a representative where the
two smaller classes are disjoint, hence tile `A₀`.  `W3FourDisjointness`
produces such a representative from any datum of the case. -/
structure PositionOne (data : GluingDatum target degree) (wall : target.V)
    extends FourStarGeometry data wall where
  /-- Position I's requirement: `e₂` and `e₃` are disjoint subsets of `[d]`. -/
  disjoint : Disjoint ((data.edgePartition growTarget).block growAnchor)
    ((data.edgePartition otherTarget).block otherAnchor)

namespace PositionOne

variable (position : PositionOne data wall)

theorem grow_not_rel_otherAnchor :
    ¬(data.edgePartition position.growTarget).Rel position.growAnchor
      position.otherAnchor := by
  intro hRel
  exact (Finset.disjoint_left.mp position.disjoint
    (((data.edgePartition position.growTarget).mem_block_iff _ _).mpr hRel))
    (((data.edgePartition position.otherTarget).mem_block_iff _ _).mpr rfl)

/-- Position I's endpoint and new-edge partition: the wall partition with `A₀`
split into `e₂` and its complement. -/
noncomputable def fine : SheetPartition degree :=
  splitAlong (data.vertexPartition wall) (data.edgePartition position.growTarget)
    position.growAnchor position.otherAnchor position.other_wall_rel
    position.grow_not_rel_otherAnchor

theorem fine_refines : position.fine.Refines (data.vertexPartition wall) :=
  splitAlong_refines _ _

theorem grow_refines_fine :
    (data.edgePartition position.growTarget).Refines position.fine := by
  refine refines_splitAlong _ _ _ position.toFourStarGeometry.grow_refines ?_
  intro first second _ hRel
  exact ⟨fun h ↦ h.trans hRel, fun h ↦ h.trans hRel.symm⟩

/-- Every sheet of `A₀` either has a singleton `t₃` class or lies in `e₃`. -/
theorem other_singleton_or_block {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel position.growAnchor first)
    (hRel : (data.edgePartition position.otherTarget).Rel first second) :
    first = second ∨
      ((data.edgePartition position.otherTarget).Rel position.otherAnchor first ∧
        (data.edgePartition position.otherTarget).Rel position.otherAnchor second) := by
  by_cases hBlock :
      (data.edgePartition position.otherTarget).Rel position.otherAnchor first
  · exact Or.inr ⟨hBlock, hBlock.trans hRel⟩
  · left
    have hCard := position.toFourStarGeometry.other_singletons first hFirst hBlock
    have hSingleton :=
      (data.edgePartition position.otherTarget).block_eq_singleton_of_blockCard_eq_one
        first hCard
    have hMem := ((data.edgePartition position.otherTarget).mem_block_iff first
      second).mpr hRel
    rw [hSingleton, Finset.mem_singleton] at hMem
    exact hMem.symm

theorem other_refines_fine :
    (data.edgePartition position.otherTarget).Refines position.fine := by
  refine refines_splitAlong _ _ _ position.toFourStarGeometry.other_refines ?_
  intro first second hFirst hRel
  rcases position.other_singleton_or_block hFirst hRel with rfl | ⟨hFirstBlock, hSecondBlock⟩
  · exact Iff.rfl
  · have hFirstOff : ¬(data.edgePartition position.growTarget).Rel
        position.growAnchor first := by
      intro hGrow
      exact (Finset.disjoint_left.mp position.disjoint
        (((data.edgePartition position.growTarget).mem_block_iff _ _).mpr hGrow))
        (((data.edgePartition position.otherTarget).mem_block_iff _ _).mpr hFirstBlock)
    have hSecondOff : ¬(data.edgePartition position.growTarget).Rel
        position.growAnchor second := by
      intro hGrow
      exact (Finset.disjoint_left.mp position.disjoint
        (((data.edgePartition position.growTarget).mem_block_iff _ _).mpr hGrow))
        (((data.edgePartition position.otherTarget).mem_block_iff _ _).mpr hSecondBlock)
    exact iff_of_false hFirstOff hSecondOff

/-- `|e'| = k₂`. -/
theorem fine_blockCard_growAnchor :
    position.fine.blockCard position.growAnchor =
      (data.edgePartition position.growTarget).blockCard position.growAnchor :=
  splitAlong_blockCard_pivot _ _ position.toFourStarGeometry.grow_refines

/-- `|e''| = k₃`. -/
theorem fine_blockCard_otherAnchor :
    position.fine.blockCard position.otherAnchor =
      (data.edgePartition position.otherTarget).blockCard position.otherAnchor := by
  have hSplit := splitAlong_blockCard_alt position.other_wall_rel
    position.grow_not_rel_otherAnchor position.toFourStarGeometry.grow_refines
  have hSum := position.toFourStarGeometry.index_sum
  change position.fine.blockCard position.otherAnchor +
    (data.edgePartition position.growTarget).blockCard position.growAnchor =
      (data.vertexPartition wall).blockCard position.growAnchor at hSplit
  omega

/-- The `e₂` block of the Position I partition is literally `e₂`. -/
theorem fine_rel_growAnchor_iff {sheet : Fin degree} :
    position.fine.Rel position.growAnchor sheet ↔
      (data.edgePartition position.growTarget).Rel position.growAnchor sheet := by
  have hBlock := splitAlong_block_pivot position.other_wall_rel
    position.grow_not_rel_otherAnchor position.toFourStarGeometry.grow_refines
  change position.fine.block position.growAnchor =
    (data.edgePartition position.growTarget).block position.growAnchor at hBlock
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff, hBlock]

/-- Its other block is exactly the rest of `A₀`. -/
theorem fine_rel_otherAnchor_iff {sheet : Fin degree} :
    position.fine.Rel position.otherAnchor sheet ↔
      ((data.vertexPartition wall).Rel position.growAnchor sheet ∧
        ¬(data.edgePartition position.growTarget).Rel position.growAnchor sheet) := by
  have hBlock := splitAlong_block_alt position.other_wall_rel
    position.grow_not_rel_otherAnchor (fine := data.edgePartition position.growTarget)
  change position.fine.block position.otherAnchor =
    (data.vertexPartition wall).block position.growAnchor \
      (data.edgePartition position.growTarget).block position.growAnchor at hBlock
  rw [← SheetPartition.mem_block_iff, hBlock, Finset.mem_sdiff,
    SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]

/-- Sheets of `e₂` carry singleton `t₃` classes: that is Position I's
disjointness, read as a count. -/
theorem other_blockCard_eq_one_of_grow {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel position.growAnchor sheet)
    (hGrow : (data.edgePartition position.growTarget).Rel position.growAnchor sheet) :
    (data.edgePartition position.otherTarget).blockCard sheet = 1 := by
  refine position.toFourStarGeometry.other_singletons sheet hSheet ?_
  intro hOther
  exact (Finset.disjoint_left.mp position.disjoint
    (((data.edgePartition position.growTarget).mem_block_iff _ _).mpr hGrow))
    (((data.edgePartition position.otherTarget).mem_block_iff _ _).mpr hOther)

/-- **The trivalent Riemann--Hurwitz census of `M⁽¹⁾`, with equality.**  On
`e₂` the three induced counts are `1`, `1`, `k₂`; on `e₃` they are `1`, `k₃`,
`1`. -/
theorem rightCounts (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel position.growAnchor sheet) :
    position.fine.blockCountWithin position.fine sheet +
        (data.edgePartition position.growTarget).blockCountWithin
          position.fine sheet +
        (data.edgePartition position.otherTarget).blockCountWithin
          position.fine sheet ≥
      position.fine.blockCard sheet + 2 := by
  have hSelf := SheetPartition.blockCountWithin_self position.fine sheet
  have hWall : ∀ s, position.fine.Rel sheet s →
      (data.vertexPartition wall).Rel position.growAnchor s := by
    intro s hs
    exact hSheet.trans (position.fine_refines.rel hs)
  by_cases hGrow :
      (data.edgePartition position.growTarget).Rel position.growAnchor sheet
  · have hFineGrow : position.fine.Rel position.growAnchor sheet :=
      position.fine_rel_growAnchor_iff.mpr hGrow
    have hInside : ∀ s, position.fine.Rel sheet s →
        (data.edgePartition position.growTarget).Rel position.growAnchor s :=
      fun s hs ↦ position.fine_rel_growAnchor_iff.mp (hFineGrow.trans hs)
    have hCountGrow := blockCountWithin_of_singletons_off_block
      (data.edgePartition position.growTarget) position.fine
      position.grow_refines_fine sheet position.growAnchor hFineGrow.symm
      (fun s hs hOff ↦ position.toFourStarGeometry.grow_singletons s (hWall s hs) hOff)
    have hCountOther := blockCountWithin_of_singletons_off_block
      (data.edgePartition position.otherTarget) position.fine
      position.other_refines_fine sheet position.growAnchor hFineGrow.symm
      (fun s hs _ ↦ position.other_blockCard_eq_one_of_grow (hWall s hs) (hInside s hs))
    have hOne := position.other_blockCard_eq_one_of_grow hSheet hGrow
    have hOneAnchor := position.other_blockCard_eq_one_of_grow
      (show (data.vertexPartition wall).Rel position.growAnchor position.growAnchor
        from rfl) rfl
    have hCard : position.fine.blockCard sheet =
        (data.edgePartition position.growTarget).blockCard position.growAnchor := by
      rw [← SheetPartition.blockCard_congr position.fine hFineGrow,
        position.fine_blockCard_growAnchor]
    omega
  · have hFineOther : position.fine.Rel position.otherAnchor sheet :=
      position.fine_rel_otherAnchor_iff.mpr ⟨hSheet, hGrow⟩
    have hOutside : ∀ s, position.fine.Rel sheet s →
        ¬(data.edgePartition position.growTarget).Rel position.growAnchor s :=
      fun s hs ↦ (position.fine_rel_otherAnchor_iff.mp (hFineOther.trans hs)).2
    have hCountGrow := blockCountWithin_of_singletons_off_block
      (data.edgePartition position.growTarget) position.fine
      position.grow_refines_fine sheet sheet rfl
      (fun s hs _ ↦ position.toFourStarGeometry.grow_singletons s (hWall s hs)
        (hOutside s hs))
    have hCountOther := blockCountWithin_of_singletons_off_block
      (data.edgePartition position.otherTarget) position.fine
      position.other_refines_fine sheet position.otherAnchor hFineOther.symm
      (fun s hs hOff ↦ position.toFourStarGeometry.other_singletons s (hWall s hs) hOff)
    have hGrowOne : (data.edgePartition position.growTarget).blockCard sheet = 1 :=
      position.toFourStarGeometry.grow_singletons sheet hSheet hGrow
    have hCard : position.fine.blockCard sheet =
        (data.edgePartition position.otherTarget).blockCard position.otherAnchor := by
      rw [← SheetPartition.blockCard_congr position.fine hFineOther,
        position.fine_blockCard_otherAnchor]
    omega

/-! ### Assembling `M⁽¹⁾` -/

/-- **Figure 28's `M⁽¹⁾`.**  The whole wall block stays at the divalent
endpoint beside `t₄`; the new edge and the trivalent endpoint both carry the
two-block split of `A₀` into `e₂` and `e₃`, beside `t₂` and `t₃`. -/
noncomputable def candidate : BalancedGlobal.Candidate target degree data wall :=
  position.toFourStarGeometry.reversedCandidate position.fine position.fine_refines
    position.grow_refines_fine position.other_refines_fine position.rightCounts

/-- `M⁽¹⁾` is valid whenever the datum it is built on is. -/
theorem candidate_valid (hValid : data.Valid) : position.candidate.datum.Valid :=
  FourStarGeometry.reversedCandidate_valid _ _ _ _ _ _ hValid

/-- `M⁽¹⁾` preserves the complete quotient-source genus. -/
theorem candidate_sourceGenus :
    genus position.candidate.datum.sourceGraph = genus data.sourceGraph :=
  FourStarGeometry.reversedCandidate_sourceGenus _ _ _ _ _ _

/-- **Figure 28's displayed `M⁽¹⁾` indices**: over the distinguished wall block
the new edge carries the two classes `|e'| = k₂` and `|e''| = k₃`. -/
theorem candidate_newEdge_blockCard :
    (position.candidate.resolution position.growAnchor).newEdge.blockCard
        position.growAnchor =
      (data.edgePartition position.growTarget).blockCard position.growAnchor ∧
    (position.candidate.resolution position.growAnchor).newEdge.blockCard
        position.otherAnchor =
      (data.edgePartition position.otherTarget).blockCard position.otherAnchor := by
  rw [show position.candidate = position.toFourStarGeometry.reversedCandidate
      position.fine position.fine_refines position.grow_refines_fine
      position.other_refines_fine position.rightCounts from rfl,
    FourStarGeometry.reversedCandidate_newEdge _ _ _ _ _ _ rfl]
  exact ⟨position.fine_blockCard_growAnchor, position.fine_blockCard_otherAnchor⟩

end PositionOne

/-! ## Figure 28's `M⁽²⁾`: Position II.b

Position II.b (Part I, case `{w3-r1-nd3-t2}`) puts the `nd = 3` vertex `A⁽²⁾` above the
trivalent endpoint `v`.  Its unique non-dangling new-edge class `e'` satisfies
`|A'| = |e'| + 1` and `|A'| = |e₄| = k₄ = |A₀|`, so `A'` is the whole wall
block at the divalent endpoint and `e' = A⁽²⁾` has `|A₀| - 1 = k₂ + k₃ - 1`
sheets.  `A⁽²⁾` is incident to both `e₂` and `e₃`, so the single sheet of `A₀`
outside it lies outside both smaller classes.  By
`W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint` such a sheet
exists precisely when `e₂` and `e₃` meet -- the gauge condition opposite to
Position I's. -/

/-- Figure 28's `M⁽²⁾` data: the case geometry together with the sheet of `A₀`
that Position II.b leaves outside `A⁽²⁾`. -/
structure PositionTwo (data : GluingDatum target degree) (wall : target.V)
    extends FourStarGeometry data wall where
  /-- The single sheet of `A₀` outside `A⁽²⁾`. -/
  outside : Fin degree
  outside_wall : (data.vertexPartition wall).Rel growAnchor outside
  outside_grow : ¬(data.edgePartition growTarget).Rel growAnchor outside
  outside_other : ¬(data.edgePartition otherTarget).Rel otherAnchor outside

/-- **Position II.b is available exactly when Position I is not.**  If the two
smaller classes meet then, their cardinalities summing to `|A₀|`, some sheet of
`A₀` lies outside both.  This is the `←` direction of
`W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint`, restated for
the packaged geometry. -/
theorem exists_outside_sheet (geometry : FourStarGeometry data wall)
    (hMeet : ¬Disjoint ((data.edgePartition geometry.growTarget).block
        geometry.growAnchor)
      ((data.edgePartition geometry.otherTarget).block geometry.otherAnchor)) :
    ∃ sheet, (data.vertexPartition wall).Rel geometry.growAnchor sheet ∧
      ¬(data.edgePartition geometry.growTarget).Rel geometry.growAnchor sheet ∧
      ¬(data.edgePartition geometry.otherTarget).Rel geometry.otherAnchor sheet := by
  classical
  set growBlock := (data.edgePartition geometry.growTarget).block geometry.growAnchor
  set otherBlock :=
    (data.edgePartition geometry.otherTarget).block geometry.otherAnchor
  set wallBlock := (data.vertexPartition wall).block geometry.growAnchor
  have hGrowSub : growBlock ⊆ wallBlock := by
    intro sheet hSheet
    exact ((data.vertexPartition wall).mem_block_iff _ _).mpr
      (geometry.grow_refines.rel
        (((data.edgePartition geometry.growTarget).mem_block_iff _ _).mp hSheet))
  have hOtherSub : otherBlock ⊆ wallBlock := by
    intro sheet hSheet
    exact ((data.vertexPartition wall).mem_block_iff _ _).mpr
      (geometry.other_wall_rel.trans (geometry.other_refines.rel
        (((data.edgePartition geometry.otherTarget).mem_block_iff _ _).mp hSheet)))
  have hUnionSub : growBlock ∪ otherBlock ⊆ wallBlock :=
    Finset.union_subset hGrowSub hOtherSub
  have hCards : growBlock.card + otherBlock.card = wallBlock.card := geometry.index_sum
  have hInter := Finset.card_union_add_card_inter growBlock otherBlock
  obtain ⟨witness, hWitnessGrow, hWitnessOther⟩ := Finset.not_disjoint_iff.mp hMeet
  have hInterPos : 0 < (growBlock ∩ otherBlock).card :=
    Finset.card_pos.mpr ⟨witness, Finset.mem_inter.mpr ⟨hWitnessGrow, hWitnessOther⟩⟩
  have hNe : growBlock ∪ otherBlock ≠ wallBlock := by
    intro hEq
    rw [hEq] at hInter
    omega
  obtain ⟨sheet, hMem, hNotMem⟩ := (Finset.ssubset_iff_of_subset hUnionSub).mp
    (Finset.ssubset_iff_subset_ne.mpr ⟨hUnionSub, hNe⟩)
  simp only [Finset.mem_union, not_or] at hNotMem
  exact ⟨sheet, ((data.vertexPartition wall).mem_block_iff _ _).mp hMem,
    fun h ↦ hNotMem.1
      (((data.edgePartition geometry.growTarget).mem_block_iff _ _).mpr h),
    fun h ↦ hNotMem.2
      (((data.edgePartition geometry.otherTarget).mem_block_iff _ _).mpr h)⟩

namespace PositionTwo

variable (position : PositionTwo data wall)

theorem outside_ne_growAnchor : position.outside ≠ position.growAnchor := by
  intro hEq
  exact position.outside_grow (hEq ▸ (rfl : (data.edgePartition
    position.growTarget).Rel position.growAnchor position.growAnchor))

theorem outside_ne_otherAnchor : position.outside ≠ position.otherAnchor := by
  intro hEq
  exact position.outside_other (hEq ▸ (rfl : (data.edgePartition
    position.otherTarget).Rel position.otherAnchor position.otherAnchor))

/-- Position II.b's endpoint and new-edge partition: the wall partition with
the outside sheet detached from `A₀`. -/
noncomputable def fine : SheetPartition degree :=
  (data.vertexPartition wall).detachSheet position.outside position.growAnchor
    position.outside_ne_growAnchor position.outside_wall.symm

theorem fine_refines : position.fine.Refines (data.vertexPartition wall) :=
  SheetPartition.detachSheet_refines _ _ _ _ _

theorem grow_blockCard_outside :
    (data.edgePartition position.growTarget).block position.outside =
      {position.outside} :=
  SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _
    (position.toFourStarGeometry.grow_singletons position.outside
      position.outside_wall position.outside_grow)

theorem other_blockCard_outside :
    (data.edgePartition position.otherTarget).block position.outside =
      {position.outside} :=
  SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _
    (position.toFourStarGeometry.other_singletons position.outside
      position.outside_wall position.outside_other)

theorem grow_refines_fine :
    (data.edgePartition position.growTarget).Refines position.fine :=
  SheetPartition.refines_detachSheet_of_block_singleton _ _ _ _ _ _
    position.toFourStarGeometry.grow_refines position.grow_blockCard_outside

theorem other_refines_fine :
    (data.edgePartition position.otherTarget).Refines position.fine :=
  SheetPartition.refines_detachSheet_of_block_singleton _ _ _ _ _ _
    position.toFourStarGeometry.other_refines position.other_blockCard_outside

theorem fine_block_outside : position.fine.block position.outside =
    {position.outside} :=
  SheetPartition.detachSheet_block_single _ _ _ _ _

theorem fine_blockCard_outside : position.fine.blockCard position.outside = 1 :=
  SheetPartition.detachSheet_blockCard_single _ _ _ _ _

/-- `|e'| = k₂ + k₃ - 1`: the trivalent class is the wall block minus one
sheet. -/
theorem fine_blockCard_growAnchor :
    position.fine.blockCard position.growAnchor + 1 =
      (data.edgePartition position.growTarget).blockCard position.growAnchor +
        (data.edgePartition position.otherTarget).blockCard position.otherAnchor := by
  have hCard := SheetPartition.detachSheet_blockCard_remainder
    (data.vertexPartition wall) position.outside position.growAnchor
    position.outside_ne_growAnchor position.outside_wall.symm
  have hCongr : (data.vertexPartition wall).blockCard position.outside =
      (data.vertexPartition wall).blockCard position.growAnchor :=
    SheetPartition.blockCard_congr _ position.outside_wall.symm
  have hPos := (data.vertexPartition wall).blockCard_pos position.growAnchor
  have hSum := position.toFourStarGeometry.index_sum
  change position.fine.blockCard position.growAnchor =
    (data.vertexPartition wall).blockCard position.outside - 1 at hCard
  omega

/-- Every sheet of `A₀` other than the detached one lies in the trivalent
class. -/
theorem fine_rel_growAnchor_iff {sheet : Fin degree} :
    position.fine.Rel position.growAnchor sheet ↔
      (sheet ≠ position.outside ∧
        (data.vertexPartition wall).Rel position.growAnchor sheet) := by
  have hBlock := SheetPartition.detachSheet_block_remainder
    (data.vertexPartition wall) position.outside position.growAnchor
    position.outside_ne_growAnchor position.outside_wall.symm
  change position.fine.block position.growAnchor =
    ((data.vertexPartition wall).block position.outside).erase position.outside
      at hBlock
  rw [← SheetPartition.mem_block_iff, hBlock, Finset.mem_erase,
    SheetPartition.mem_block_iff]
  exact and_congr Iff.rfl
    ⟨fun h ↦ position.outside_wall.trans h, fun h ↦ position.outside_wall.symm.trans h⟩

/-- **The trivalent Riemann--Hurwitz census of `M⁽²⁾`, with equality.**  On
`A⁽²⁾` the three induced counts are `1`, `k₃`, `k₂`; on the detached singleton
they are `1`, `1`, `1`. -/
theorem rightCounts (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel position.growAnchor sheet) :
    position.fine.blockCountWithin position.fine sheet +
        (data.edgePartition position.growTarget).blockCountWithin
          position.fine sheet +
        (data.edgePartition position.otherTarget).blockCountWithin
          position.fine sheet ≥
      position.fine.blockCard sheet + 2 := by
  have hSelf := SheetPartition.blockCountWithin_self position.fine sheet
  by_cases hOutside : sheet = position.outside
  · subst sheet
    have hGrowOne := SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
      (data.edgePartition position.growTarget) position.fine position.outside
      position.fine_block_outside
    have hOtherOne := SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
      (data.edgePartition position.otherTarget) position.fine position.outside
      position.fine_block_outside
    have hCardOne := position.fine_blockCard_outside
    omega
  · have hRel : position.fine.Rel position.growAnchor sheet :=
      position.fine_rel_growAnchor_iff.mpr ⟨hOutside, hSheet⟩
    have hWall : ∀ s, position.fine.Rel sheet s →
        (data.vertexPartition wall).Rel position.growAnchor s :=
      fun s hs ↦ hSheet.trans (position.fine_refines.rel hs)
    have hOtherAnchor : position.fine.Rel sheet position.otherAnchor := by
      refine hRel.symm.trans (position.fine_rel_growAnchor_iff.mpr ⟨?_, ?_⟩)
      · exact fun h ↦ position.outside_ne_otherAnchor h.symm
      · exact position.other_wall_rel
    have hCountGrow := blockCountWithin_of_singletons_off_block
      (data.edgePartition position.growTarget) position.fine
      position.grow_refines_fine sheet position.growAnchor hRel.symm
      (fun s hs hOff ↦ position.toFourStarGeometry.grow_singletons s (hWall s hs) hOff)
    have hCountOther := blockCountWithin_of_singletons_off_block
      (data.edgePartition position.otherTarget) position.fine
      position.other_refines_fine sheet position.otherAnchor hOtherAnchor
      (fun s hs hOff ↦ position.toFourStarGeometry.other_singletons s (hWall s hs) hOff)
    have hCard : position.fine.blockCard sheet =
        position.fine.blockCard position.growAnchor :=
      (SheetPartition.blockCard_congr position.fine hRel).symm
    have hSize := position.fine_blockCard_growAnchor
    omega

/-! ### Assembling `M⁽²⁾` -/

/-- **Figure 28's `M⁽²⁾`.**  The whole wall block stays at the divalent
endpoint beside `t₄`; the new edge and the trivalent endpoint carry `A₀` with
one sheet detached, beside `t₂` and `t₃`. -/
noncomputable def candidate : BalancedGlobal.Candidate target degree data wall :=
  position.toFourStarGeometry.reversedCandidate position.fine position.fine_refines
    position.grow_refines_fine position.other_refines_fine position.rightCounts

/-- `M⁽²⁾` is valid whenever the datum it is built on is. -/
theorem candidate_valid (hValid : data.Valid) : position.candidate.datum.Valid :=
  FourStarGeometry.reversedCandidate_valid _ _ _ _ _ _ hValid

/-- `M⁽²⁾` preserves the complete quotient-source genus. -/
theorem candidate_sourceGenus :
    genus position.candidate.datum.sourceGraph = genus data.sourceGraph :=
  FourStarGeometry.reversedCandidate_sourceGenus _ _ _ _ _ _

/-- **Figure 28's displayed `M⁽²⁾` index**: over the distinguished wall block
the new edge carries the class `|e'| = k₄ - 1 = k₂ + k₃ - 1`. -/
theorem candidate_newEdge_blockCard :
    (position.candidate.resolution position.growAnchor).newEdge.blockCard
          position.growAnchor + 1 =
      (data.edgePartition position.growTarget).blockCard position.growAnchor +
        (data.edgePartition position.otherTarget).blockCard position.otherAnchor := by
  rw [show position.candidate = position.toFourStarGeometry.reversedCandidate
      position.fine position.fine_refines position.grow_refines_fine
      position.other_refines_fine position.rightCounts from rfl,
    FourStarGeometry.reversedCandidate_newEdge _ _ _ _ _ _ rfl]
  exact position.fine_blockCard_growAnchor

end PositionTwo

/-! ## Both members on branch-swapped copies of one datum

`W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint` shows that
Position I and Position II.b cannot be realized on one fixed sheet labelling.
`W3FourDisjointness` shows that `Disjoint e₂ e₃` is a gauge: the branch swap of
Draisma--Vargas Part I (§3.2) along the branch through `t₃` fixes `A₀`, `e₂` and
`e₄` as terms and moves `e₃` freely inside `A₀`. The two theorems below combine
them: on one and the same wall datum, one branch swap produces a representative
carrying `M⁽¹⁾` and another produces a representative carrying `M⁽²⁾`.

The three branch flags are carried explicitly, exactly as `W3FourDisjointness`
leaves them: they say that the moved component contains `t₃` and neither `t₂`
nor `t₄`.  On a target tree they hold with `root` the far endpoint of `t₃`, and
`TargetBranchRegion.vertexMoved` decides them on any concrete target;
`ThirdEquation.W3SourceInput` carries no target acyclicity, so they are not
derived here. -/

section GaugeCopies

variable (geometry : FourStarGeometry data wall) (root : target.V)
  (hRoot : root ≠ wall)

/-- The Position I data on a branch-swapped copy, named so that its member's
receipts can be read off. -/
noncomputable def swappedPositionOne
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.growTarget = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.largestTarget = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.otherTarget = true)
    (hDisjoint : Disjoint
      (((branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
        geometry.growTarget).block geometry.growAnchor)
      (((branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
        geometry.otherTarget).block (permutation geometry.otherAnchor))) :
    PositionOne (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall where
  toFourStarGeometry := geometry.swap root hRoot permutation hFix hGrowFixed
    hLargestFixed hOtherMoved
  disjoint := hDisjoint

/-- The Position II.b data on a branch-swapped copy, named for the same
reason. -/
noncomputable def swappedPositionTwo
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.growTarget = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.largestTarget = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.otherTarget = true)
    (outside : Fin degree)
    (hWall : (data.vertexPartition wall).Rel geometry.growAnchor outside)
    (hGrow : ¬((branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
      geometry.growTarget).Rel geometry.growAnchor outside)
    (hOther : ¬((branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
      geometry.otherTarget).Rel (permutation geometry.otherAnchor) outside) :
    PositionTwo (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall where
  toFourStarGeometry := geometry.swap root hRoot permutation hFix hGrowFixed
    hLargestFixed hOtherMoved
  outside := outside
  outside_wall := by
    rw [branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix]
    exact hWall
  outside_grow := hGrow
  outside_other := hOther

/-- **Gauge move A gives `M⁽¹⁾`.**  A series of branch-swaps inside `A₀`
along the branch through `t₃` carries `e₃` off `e₂`, and the resulting
representative carries Figure 28's Position I member: valid, genus preserving,
and with the two displayed new-edge classes of sizes `k₂` and `k₃` -- the
*original* indices, since the swap fixes `e₂` as a term and preserves `e₃`'s
cardinality. -/
theorem exists_member_one
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.growTarget = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.largestTarget = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.otherTarget = true) :
    ∃ (permutation : Equiv.Perm (Fin degree))
      (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
      (position : PositionOne
        (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall),
      BranchGauge data wall root hRoot
          (branchSwapOfPerm data wall root hRoot permutation hFix) ∧
        position.toFourStarGeometry = geometry.swap root hRoot permutation hFix
          hGrowFixed hLargestFixed hOtherMoved ∧
        (data.Valid → position.candidate.datum.Valid) ∧
        genus position.candidate.datum.sourceGraph =
          genus (branchSwapOfPerm data wall root hRoot permutation
            hFix).apply.sourceGraph ∧
        (position.candidate.resolution geometry.growAnchor).newEdge.blockCard
            geometry.growAnchor =
          (data.edgePartition geometry.growTarget).blockCard geometry.growAnchor ∧
        (position.candidate.resolution geometry.growAnchor).newEdge.blockCard
            (permutation geometry.otherAnchor) =
          (data.edgePartition geometry.otherTarget).blockCard
            geometry.otherAnchor := by
  classical
  obtain ⟨permutation, hInside, hOutside, hDisjoint⟩ :=
    exists_perm_image_disjoint ((data.vertexPartition wall).block geometry.growAnchor)
      ((data.edgePartition geometry.growTarget).block geometry.growAnchor)
      ((data.edgePartition geometry.otherTarget).block geometry.otherAnchor)
      (block_subset_wallBlock data wall geometry.growTarget geometry.growAnchor
        geometry.growAnchor geometry.grow_refines rfl)
      (block_subset_wallBlock data wall geometry.otherTarget geometry.growAnchor
        geometry.otherAnchor geometry.other_refines geometry.other_wall_rel)
      geometry.index_sum
  have hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet :=
    rel_of_stabilizes_block (data.vertexPartition wall) geometry.growAnchor
      permutation hInside hOutside
  have hDisjointSwapped : Disjoint
      (((branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
        geometry.growTarget).block geometry.growAnchor)
      (((branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
        geometry.otherTarget).block (permutation geometry.otherAnchor)) := by
    rw [branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot permutation hFix
        geometry.growTarget hGrowFixed,
      branchSwapOfPerm_edgePartition_of_moved data wall root hRoot permutation hFix
        geometry.otherTarget hOtherMoved, SheetPartition.relabel_block]
    exact hDisjoint
  have hStepGrow : ((branchSwapOfPerm data wall root hRoot permutation
        hFix).apply.edgePartition geometry.growTarget).blockCard
        geometry.growAnchor =
      (data.edgePartition geometry.growTarget).blockCard geometry.growAnchor := by
    rw [branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot permutation hFix
      geometry.growTarget hGrowFixed]
  have hStepOther : ((branchSwapOfPerm data wall root hRoot permutation
        hFix).apply.edgePartition geometry.otherTarget).blockCard
        (permutation geometry.otherAnchor) =
      (data.edgePartition geometry.otherTarget).blockCard geometry.otherAnchor := by
    rw [branchSwapOfPerm_edgePartition_of_moved data wall root hRoot permutation hFix
      geometry.otherTarget hOtherMoved]
    exact SheetPartition.relabel_blockCard _ permutation geometry.otherAnchor
  refine ⟨permutation, hFix,
    swappedPositionOne geometry root hRoot permutation hFix hGrowFixed
      hLargestFixed hOtherMoved hDisjointSwapped,
    branchSwapOfPerm_branchGauge data wall root hRoot permutation hFix, rfl,
    fun hValid ↦ PositionOne.candidate_valid _
      ((branchSwapOfPerm_branchGauge data wall root hRoot permutation hFix).valid
        hValid),
    PositionOne.candidate_sourceGenus _, ?_, ?_⟩
  · exact (PositionOne.candidate_newEdge_blockCard (swappedPositionOne geometry root
      hRoot permutation hFix hGrowFixed hLargestFixed hOtherMoved
      hDisjointSwapped)).1.trans hStepGrow
  · exact (PositionOne.candidate_newEdge_blockCard (swappedPositionOne geometry root
      hRoot permutation hFix hGrowFixed hLargestFixed hOtherMoved
      hDisjointSwapped)).2.trans hStepOther

/-- **Gauge move B gives `M⁽²⁾`.**  One branch-swap by the transposition of
the two class anchors drags `e₃` across `e₂`, and the resulting representative
carries Figure 28's Position II.b member: valid, genus preserving, and with the
displayed new-edge class of size `k₄ - 1 = k₂ + k₃ - 1`. -/
theorem exists_member_two
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.growTarget = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.largestTarget = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.otherTarget = true) :
    ∃ (permutation : Equiv.Perm (Fin degree))
      (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
      (position : PositionTwo
        (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall),
      BranchGauge data wall root hRoot
          (branchSwapOfPerm data wall root hRoot permutation hFix) ∧
        position.toFourStarGeometry = geometry.swap root hRoot permutation hFix
          hGrowFixed hLargestFixed hOtherMoved ∧
        (data.Valid → position.candidate.datum.Valid) ∧
        genus position.candidate.datum.sourceGraph =
          genus (branchSwapOfPerm data wall root hRoot permutation
            hFix).apply.sourceGraph ∧
        (position.candidate.resolution geometry.growAnchor).newEdge.blockCard
              geometry.growAnchor + 1 =
          (data.edgePartition geometry.growTarget).blockCard geometry.growAnchor +
            (data.edgePartition geometry.otherTarget).blockCard
              geometry.otherAnchor := by
  classical
  have hFix : ∀ sheet, (data.vertexPartition wall).Rel
      ((Equiv.swap geometry.growAnchor geometry.otherAnchor) sheet) sheet :=
    (data.vertexPartition wall).swap_apply_rel_self_of_rel geometry.other_wall_rel
  have hSwap : (Equiv.swap geometry.growAnchor geometry.otherAnchor)
      geometry.otherAnchor = geometry.growAnchor :=
    Equiv.swap_apply_right geometry.growAnchor geometry.otherAnchor
  have hMeet : ¬Disjoint
      (((branchSwapOfPerm data wall root hRoot _ hFix).apply.edgePartition
        geometry.growTarget).block geometry.growAnchor)
      (((branchSwapOfPerm data wall root hRoot _ hFix).apply.edgePartition
        geometry.otherTarget).block
          ((Equiv.swap geometry.growAnchor geometry.otherAnchor)
            geometry.otherAnchor)) := by
    rw [branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot _ hFix
        geometry.growTarget hGrowFixed,
      branchSwapOfPerm_edgePartition_of_moved data wall root hRoot _ hFix
        geometry.otherTarget hOtherMoved, SheetPartition.relabel_block]
    refine Finset.not_disjoint_iff.mpr ⟨geometry.growAnchor,
      ((data.edgePartition geometry.growTarget).mem_block_iff _ _).mpr rfl, ?_⟩
    exact Finset.mem_image.mpr ⟨geometry.otherAnchor,
      ((data.edgePartition geometry.otherTarget).mem_block_iff _ _).mpr rfl, hSwap⟩
  obtain ⟨sheet, hSheetWall, hSheetGrow, hSheetOther⟩ :=
    exists_outside_sheet (geometry.swap root hRoot _ hFix hGrowFixed hLargestFixed
      hOtherMoved) hMeet
  refine ⟨_, hFix,
    swappedPositionTwo geometry root hRoot _ hFix hGrowFixed hLargestFixed
      hOtherMoved sheet
      (by
        rw [branchSwapOfPerm_vertexPartition_wall data wall root hRoot _ hFix]
          at hSheetWall
        exact hSheetWall)
      hSheetGrow hSheetOther,
    branchSwapOfPerm_branchGauge data wall root hRoot _ hFix, rfl,
    fun hValid ↦ PositionTwo.candidate_valid _
      ((branchSwapOfPerm_branchGauge data wall root hRoot _ hFix).valid hValid),
    PositionTwo.candidate_sourceGenus _, ?_⟩
  refine (PositionTwo.candidate_newEdge_blockCard _).trans ?_
  have hGrowEq := congrArg (fun partition ↦ SheetPartition.blockCard partition
    geometry.growAnchor) (branchSwapOfPerm_edgePartition_of_fixed data wall root
      hRoot _ hFix geometry.growTarget hGrowFixed)
  have hOtherEq := (congrArg (fun partition ↦ SheetPartition.blockCard partition
    ((Equiv.swap geometry.growAnchor geometry.otherAnchor) geometry.otherAnchor))
      (branchSwapOfPerm_edgePartition_of_moved data wall root hRoot _ hFix
        geometry.otherTarget hOtherMoved)).trans
    (SheetPartition.relabel_blockCard _
      (Equiv.swap geometry.growAnchor geometry.otherAnchor) geometry.otherAnchor)
  exact congrArg₂ (· + ·) hGrowEq hOtherEq

end GaugeCopies

/-! ## Equation (2)

Figure 28's four determinants are

  `c⁽¹⁾ = c(e₂)/k₂ + c(e₃)/k₃ + σ₀(J₀,4)`,  `c⁽²⁾ = c(e₄)/(k₂+k₃−1) + σ₀(J₀,4)`,
  `c⁽³⁾ = c(e₂)/(k₂+1) + σ₀(J₀,2)`,          `c⁽⁴⁾ = c(e₃)/(k₃+1) + σ₀(J₀,3)`,

and Equation (2) is `c⁽¹⁾ + (k₂+k₃−1)c⁽²⁾ + (k₂+1)c⁽³⁾ + (k₃+1)c⁽⁴⁾ = 0`.  The
identity itself is `BalancingRemaining.balance_w3_a_eq_k4`; what is added here
is the assembly into a `BalancedGlobal.Family` over the *original* datum, and
the exactness check below. -/

section Equation

/-- Re-base a certified candidate of a branch-swapped copy onto the original
datum.  `W3FourDisjointness.BranchGauge.valid` supplies exactly the implication
`BalancedGlobal.CertifiedCandidate` stores, so the two gauge copies' members
are members over the original datum as well.  This is the precise sense in
which the two branch-swapped copies compose with `M⁽³⁾` and `M⁽⁴⁾` into one
family. -/
noncomputable def rebase {other : GluingDatum target degree}
    (candidate : BalancedGlobal.CertifiedCandidate other)
    (hValid : data.Valid → other.Valid) :
    BalancedGlobal.CertifiedCandidate data where
  outgoingTarget := candidate.outgoingTarget
  datum := candidate.datum
  valid_of_old := fun hData ↦ candidate.valid_of_old (hValid hData)

@[simp] theorem rebase_datum {other : GluingDatum target degree}
    (candidate : BalancedGlobal.CertifiedCandidate other)
    (hValid : data.Valid → other.Valid) :
    (rebase (data := data) candidate hValid).datum = candidate.datum := rfl

/-- **Equation (2) as a determinant balance.**  Four outgoing members over one
datum whose length matrices agree away from the wall column and carry Figure
28's four determinants form a positively balanced family with the weights
`1, k₂+k₃−1, k₂+1, k₃+1`.

The three inputs `h₂`, `h₃`, `h₄` are the limit `M₀`'s own relations, displayed
beside Figure 28: `c(e_i)/k_i + σ₀(J₀,i) = 0` for `i = 2, 3` and
`c(e₄)/(k₂+k₃) + σ₀(J₀,4) = 0`.  They are satisfiable together with `hk₂`,
`hk₃` -- take `k₂ = k₃ = 1`, `s₂ = s₃ = s₄ = 0` and `c₂ = c₃ = c₄ = 0` -- and
`hDet`/`hAgree` constrain only the supplied matrices, so nothing here is
vacuous. -/
noncomputable def equationTwoFamily
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (member : Fin 4 → BalancedGlobal.CertifiedCandidate data)
    (matrix : Fin 4 → Matrix coordinate coordinate ℚ) (wallColumn : coordinate)
    {k₂ k₃ c₂ c₃ c₄ s₂ s₃ s₄ : ℚ} (hk₂ : 1 ≤ k₂) (hk₃ : 1 ≤ k₃)
    (h₂ : c₂ / k₂ + s₂ = 0) (h₃ : c₃ / k₃ + s₃ = 0)
    (h₄ : c₄ / (k₂ + k₃) + s₄ = 0)
    (hDet : ∀ i, (matrix i).det =
      ![c₂ / k₂ + c₃ / k₃ + s₄, c₄ / (k₂ + k₃ - 1) + s₄,
        c₂ / (k₂ + 1) + s₂, c₃ / (k₃ + 1) + s₃] i)
    (hAgree : ∀ first second,
      AgreeOffColumn (matrix first) (matrix second) wallColumn) :
    BalancedGlobal.Family (coordinate := coordinate) 4 data where
  candidate := member
  matrix := matrix
  wallColumn := wallColumn
  weight := ![1, k₂ + k₃ - 1, k₂ + 1, k₃ + 1]
  positiveBalance := by
    rw [funext hDet]
    exact BalancingRemaining.balance_w3_a_eq_k4 hk₂ hk₃ h₂ h₃ h₄
  agreeOffWall := hAgree

/-- **Equation (2) is exact in all four members.**  Each of the four residuals
obtained by dropping one member from the weighted sum is a nonzero combination
of the limit's own `σ₀` terms, so no three of Figure 28's members balance by
themselves: dropping `M⁽¹⁾` leaves `σ₀(J₀,2) + σ₀(J₀,3) − σ₀(J₀,4)`, dropping
`M⁽²⁾` leaves `σ₀(J₀,4)`, dropping `M⁽³⁾` leaves `−σ₀(J₀,2)` and dropping
`M⁽⁴⁾` leaves `−σ₀(J₀,3)`.  This is the independent check that the case really
does need four members. -/
theorem equationTwo_residuals {k₂ k₃ c₂ c₃ c₄ s₂ s₃ s₄ : ℚ}
    (hk₂ : 1 ≤ k₂) (hk₃ : 1 ≤ k₃)
    (h₂ : c₂ / k₂ + s₂ = 0) (h₃ : c₃ / k₃ + s₃ = 0)
    (h₄ : c₄ / (k₂ + k₃) + s₄ = 0) :
    (k₂ + k₃ - 1) * (c₄ / (k₂ + k₃ - 1) + s₄) + (k₂ + 1) * (c₂ / (k₂ + 1) + s₂) +
        (k₃ + 1) * (c₃ / (k₃ + 1) + s₃) = s₂ + s₃ - s₄ ∧
      (c₂ / k₂ + c₃ / k₃ + s₄) + (k₂ + 1) * (c₂ / (k₂ + 1) + s₂) +
        (k₃ + 1) * (c₃ / (k₃ + 1) + s₃) = s₄ ∧
      (c₂ / k₂ + c₃ / k₃ + s₄) + (k₂ + k₃ - 1) * (c₄ / (k₂ + k₃ - 1) + s₄) +
        (k₃ + 1) * (c₃ / (k₃ + 1) + s₃) = -s₂ ∧
      (c₂ / k₂ + c₃ / k₃ + s₄) + (k₂ + k₃ - 1) * (c₄ / (k₂ + k₃ - 1) + s₄) +
        (k₂ + 1) * (c₂ / (k₂ + 1) + s₂) = -s₃ := by
  have hk₂₀ : k₂ ≠ 0 := by linarith
  have hk₃₀ : k₃ ≠ 0 := by linarith
  have hksum : k₂ + k₃ ≠ 0 := by linarith
  have hksub : k₂ + k₃ - 1 ≠ 0 := by linarith
  have hk₂p1 : k₂ + 1 ≠ 0 := by linarith
  have hk₃p1 : k₃ + 1 ≠ 0 := by linarith
  have hc₂ : c₂ = -(k₂ * s₂) := by
    field_simp at h₂; linarith
  have hc₃ : c₃ = -(k₃ * s₃) := by
    field_simp at h₃; linarith
  have hc₄ : c₄ = -((k₂ + k₃) * s₄) := by
    field_simp at h₄; linarith
  subst hc₂; subst hc₃; subst hc₄
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · field_simp
      ring

end Equation

/-! ## The four-member family of case `{w3-r1-nd3-t2-(a=k₄)}` -/

section FourMembers

open W3FourSourceCandidates

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- **Figure 28's four members compose into one `BalancedGlobal.Family` over
the incoming datum.**

`M⁽³⁾` and `M⁽⁴⁾` are `W3FourSourceCandidates`' two Position II.a members on
the datum itself.  `M⁽¹⁾` and `M⁽²⁾` are built on branch-swapped copies -- the
two Figure 28 alternatives are not simultaneously available on one sheet
labelling (`W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint`) but
are on one *isomorphism class* (`W3FourDisjointness`) -- and are carried back
to the incoming datum by `rebase`, whose only input is
`W3FourDisjointness.BranchGauge.valid`.

That last step is exactly what `BalancedGlobal.Family` permits and
`BalancedGlobal.PresentedFamily` does not: `Family` stores each member as a
`CertifiedCandidate`, whose single datum-dependent field is the implication
`data.Valid → datum.Valid`, while `PresentedFamily` stores a
`BalancedGlobal.Candidate target degree data wall`, whose `exterior` and
`riemannHurwitz` fields mention `data`'s own edge partitions and so cannot be
re-based across a swap.  See the closing section for what that costs.

The determinant hypotheses are the displayed Figure 28 values against the
limit's own relations `h₂`, `h₃`, `h₄`; they are jointly satisfiable (take
`k₂ = k₃ = 1` and all of `c₂, c₃, c₄, s₂, s₃, s₄` zero, with any four equal
matrices), and the branch flags hold on any target tree with `root` the far
endpoint of `t₃`. -/
theorem exists_equationTwo_family
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (root : target.V) (hRoot : root ≠ wall)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot profile.first.1.1.1 = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot profile.largest.1.1.1 = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot profile.second.1.1.1 = true)
    (matrix : Fin 4 → Matrix coordinate coordinate ℚ) (wallColumn : coordinate)
    {k₂ k₃ c₂ c₃ c₄ s₂ s₃ s₄ : ℚ} (hk₂ : 1 ≤ k₂) (hk₃ : 1 ≤ k₃)
    (h₂ : c₂ / k₂ + s₂ = 0) (h₃ : c₃ / k₃ + s₃ = 0)
    (h₄ : c₄ / (k₂ + k₃) + s₄ = 0)
    (hDet : ∀ i, (matrix i).det =
      ![c₂ / k₂ + c₃ / k₃ + s₄, c₄ / (k₂ + k₃ - 1) + s₄,
        c₂ / (k₂ + 1) + s₂, c₃ / (k₃ + 1) + s₃] i)
    (hAgree : ∀ first second,
      AgreeOffColumn (matrix first) (matrix second) wallColumn) :
    ∃ family : BalancedGlobal.Family (coordinate := coordinate) 4 data,
      family.matrix = matrix ∧ family.wallColumn = wallColumn ∧
        family.weight = ![1, k₂ + k₃ - 1, k₂ + 1, k₃ + 1] ∧
        family.candidate 2 =
          (thirdCandidate profile directions largest_index).certified ∧
        family.candidate 3 =
          (fourthCandidate profile directions largest_index).certified := by
  classical
  let geometry : FourStarGeometry data wall :=
    ofGrowProfile (growProfileFirst profile directions largest_index)
  obtain ⟨permOne, hFixOne, positionOne, hGaugeOne, _, _, _, _, _⟩ :=
    exists_member_one geometry root hRoot hGrowFixed hLargestFixed hOtherMoved
  obtain ⟨permTwo, hFixTwo, positionTwo, hGaugeTwo, _, _, _, _⟩ :=
    exists_member_two geometry root hRoot hGrowFixed hLargestFixed hOtherMoved
  refine ⟨equationTwoFamily
    ![rebase positionOne.candidate.certified hGaugeOne.valid,
      rebase positionTwo.candidate.certified hGaugeTwo.valid,
      (thirdCandidate profile directions largest_index).certified,
      (fourthCandidate profile directions largest_index).certified]
    matrix wallColumn hk₂ hk₃ h₂ h₃ h₄ hDet hAgree, rfl, rfl, rfl, rfl, rfl⟩

end FourMembers

/-! ## The certified exit for a gauge-mixed family

`BalancedGlobal.PresentedFamily` stores each member as a
`BalancedGlobal.Candidate target degree data wall`, over one fixed `data`.
Figure 28's four members do not all live over one `data` -- `M⁽¹⁾` and `M⁽²⁾`
need opposite gauge conditions -- so they do not assemble into a
`PresentedFamily`, and `PresentedFamily.exists_valid_positive_exit_with_pencil`
does not apply to them as it stands.

Nothing essential is lost.  What that theorem actually uses of the base datum
is `data.Valid` (to validate the selected member and to clear its pencil) and
the shared `target` (for connectedness, genus and a root).  The branch swap
preserves the first (`W3FourDisjointness.BranchGauge.valid`) and does not touch
the second, so the same exit goes through for a family whose members sit over
*different* data, one per member.  `GaugeFamily` is that structure and
`GaugeFamily.exists_valid_positive_exit_with_pencil` is that theorem, proved
here by the same three steps as the original -- `exists_opposite_of_positiveBalance`,
`crosses_into_positive_cone`, `BalancedGlobal.Candidate.clearedPencil`. -/

section GaugeExit

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- A balanced family of wall resolutions whose members sit over possibly
different, but gauge-equivalent, gluing data on one target.  Setting every
`base i` to `data` recovers `BalancedGlobal.PresentedFamily`.

The structure is `BalancedGlobal.GaugeFamily`, beside
`BalancedGlobal.PresentedFamily`, with the same fields, the same positive exit,
and `BalancedGlobal.PresentedFamily.toGaugeFamily` as its constant-base
instance; `WallProgress.WallInput` and `SemanticAtlasMarch.State.PresentedProgress`
carry such gauge-mixed families.  This abbreviation provides the name used here
and downstream. -/
abbrev GaugeFamily (n : ℕ) (data : GluingDatum target degree)
    (wall : target.V) :=
  BalancedGlobal.GaugeFamily (coordinate := coordinate) n data wall

namespace GaugeFamily

/-- **The positive exit with a cleared pencil, for a gauge-mixed family.**
Verbatim `BalancedGlobal.PresentedFamily.exists_valid_positive_exit_with_pencil`,
except that each member's validity is routed through its own gauge.  The
nonsingularity gate on `hSystems` is the same one, and for the same reason:
`PositiveBalance` is a signed balance, so a member with `det = 0` need not have
a solvable velocity system, and the selected member always has `det ≠ 0`. -/
theorem exists_valid_positive_exit_with_pencil {n : ℕ}
    {data : GluingDatum target degree} {wall : target.V}
    (family : GaugeFamily (coordinate := coordinate) n data wall)
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V)
    (incoming : Fin n)
    (hincoming : (GluingDatum.LengthMatrixPresentation.matrix
      (family.presentation incoming)).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin n → coordinate → ℚ)
    (hz : z family.wallColumn = 0)
    (hzpos : ∀ i, i ≠ family.wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation incoming)).mulVec incomingVelocity =
      (GluingDatum.LengthMatrixPresentation.matrix
        (family.presentation outgoing)).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity family.wallColumn < 0) :
    ∃ outgoing,
      (family.candidate outgoing).datum.Valid ∧
      (GluingDatum.LengthMatrixPresentation.matrix
          (family.presentation incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (family.presentation outgoing)).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            (family.presentation outgoing)).mulVec
              (z + t • outgoingVelocity outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            (family.presentation incoming)).mulVec z +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              (family.presentation incoming)).mulVec incomingVelocity ∧
        Nonempty (BalancedGlobal.Candidate.ClearedPencil
          (family.candidate outgoing) (family.presentation outgoing)
          (z + t • outgoingVelocity outgoing)) := by
  obtain ⟨outgoing, hsign⟩ :=
    BalancingValencyTwo.exists_opposite_of_positiveBalance family.positiveBalance
      hincoming
  have hBaseValid : (family.base outgoing).Valid := family.valid_of_old outgoing hValid
  have hOutgoingValid := (family.candidate outgoing).datum_valid hBaseValid
  obtain ⟨δ, hδ, hstep⟩ := crosses_into_positive_cone
    (family.agreeOffWall incoming outgoing) hsign hz hzpos
    (hSystems outgoing (BalancedGlobal.det_ne_zero_of_mul_det_neg hsign))
    hIncomingDirection
  refine ⟨outgoing, hOutgoingValid, hsign, δ, hδ, ?_⟩
  intro t ht htd
  rcases hstep t ht htd with ⟨hPositive, hMetric⟩
  exact ⟨hPositive, hMetric,
    ⟨BalancedGlobal.Candidate.clearedPencil (family.candidate outgoing) hBaseValid
      hTargetConnected hTargetGenus root (family.presentation outgoing)
      (z + t • outgoingVelocity outgoing) hPositive⟩⟩

end GaugeFamily

/-- **Figure 28's four members as a gauge-mixed presented family.**  The
`base`/`gauge` pair is what `exists_member_one` and `exists_member_two` return
for `i = 0, 1` -- a branch-swapped copy together with
`W3FourDisjointness.BranchGauge.valid` -- and is `data` with `id` for
`i = 2, 3`, where `W3FourSourceCandidates` builds `M⁽³⁾` and `M⁽⁴⁾` on the
datum itself.

The remaining input is `presentation`: an honest length-matrix presentation of
each member with Figure 28's displayed determinant.  That is the **limit-matrix
half** of the case and is *not* constructed here (see `W3FourStableGraph`); it
is named as a hypothesis, which is what `hDet` and `hAgree` record.  Everything
else -- the members, their validity, their genus, their displayed new-edge
indices, and Equation (2) itself -- is proved above.

`GaugeFamily.exists_valid_positive_exit_with_pencil` then supplies the
certified exit directly. -/
noncomputable def equationTwoGaugeFamily
    (base : Fin 4 → GluingDatum target degree)
    (gauge : ∀ i, data.Valid → (base i).Valid)
    (member : ∀ i, BalancedGlobal.Candidate target degree (base i) wall)
    (presentation : ∀ i, (member i).datum.LengthMatrixPresentation coordinate)
    (wallColumn : coordinate)
    {k₂ k₃ c₂ c₃ c₄ s₂ s₃ s₄ : ℚ} (hk₂ : 1 ≤ k₂) (hk₃ : 1 ≤ k₃)
    (h₂ : c₂ / k₂ + s₂ = 0) (h₃ : c₃ / k₃ + s₃ = 0)
    (h₄ : c₄ / (k₂ + k₃) + s₄ = 0)
    (hDet : ∀ i, (GluingDatum.LengthMatrixPresentation.matrix (presentation i)).det =
      ![c₂ / k₂ + c₃ / k₃ + s₄, c₄ / (k₂ + k₃ - 1) + s₄,
        c₂ / (k₂ + 1) + s₂, c₃ / (k₃ + 1) + s₃] i)
    (hAgree : ∀ first second,
      AgreeOffColumn
        (GluingDatum.LengthMatrixPresentation.matrix (presentation first))
        (GluingDatum.LengthMatrixPresentation.matrix (presentation second))
        wallColumn) :
    GaugeFamily (coordinate := coordinate) 4 data wall where
  base := base
  valid_of_old := gauge
  candidate := member
  presentation := presentation
  wallColumn := wallColumn
  weight := ![1, k₂ + k₃ - 1, k₂ + 1, k₃ + 1]
  positiveBalance := by
    rw [funext hDet]
    exact BalancingRemaining.balance_w3_a_eq_k4 hk₂ hk₃ h₂ h₃ h₄
  agreeOffWall := hAgree

end GaugeExit
end DraismaVargas.LocalCases.W3FourClosure
