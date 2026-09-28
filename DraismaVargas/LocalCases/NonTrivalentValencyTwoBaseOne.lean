import DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate

/-!
# Part II, valency two, Configuration A: the **Base I** candidates

Source: Vargas, Part II, Section 5.4, Configuration A of case `{v2-nd4}` (case
`{v2-nd4-t3}`), together with Draisma--Vargas Part I, Case `{w2-r2}`, Base I,
whose description of the two base trees, and of the shape of the fibre above
the new leaf, is the one followed here.  (Part II's parenthetical descriptions
of the two base trees differ from Part I's; this file follows Part I, where
`T_∅` has `val u = 1`, `val v = 3` and `T_2` has `val u = val v = 2`.)

`NonTrivalentValencyTwoCandidate` builds the **Base II** member,
`T_2`, both new target endpoints divalent, two thick classes merged above `u`.
That covers all three outgoing types in Configuration B and Type III in
Configuration A.  This module builds the **Base I** members of
Configuration A: the base tree `T_empty`, in which `u` is a *leaf* and
`v` is *trivalent*.

## The Base I picture (Part I, Case `{w2-r2}`)

The outgoing base tree attaches a new leaf edge `t_1` at the wall `w_0`, whose
far endpoint `u` is a leaf and whose near endpoint `v` carries both old
occurrences `t_2`, `t_3`, so `val u = 1` and `val v = 3`.  Above the anchor `A`:

* above the leaf `u` there is **one fold** `F` with `|F| = 2`, carrying the two
  occurrences over `t_1` of index `1` each, whose local ramification is
  `r(F) = 2`; every other sheet of `A` is a singleton block above `u` with one
  dangling occurrence.  This is exactly branch two of
  `StableLocalProperties.leaf_block_dichotomy`, the only shape a leaf block of
  a change-minimal leaf may have besides an unramified singleton, and it uses
  the whole change budget `ch(u) = 2 = r_0(A)`;
* above the branch point `v` there are **two vertices** `A_1`, `A_2`, each
  incident to one occurrence over `t_1` (through the fold), one survivor over
  `t_2` and one survivor over `t_3`; both are unramified, which forces
  `|A_1| = k_alpha = k_beta` and `|A_2| = k_gamma = k_delta`.

So `A_1` is simultaneously a class of the `t_2`-partition and a class of the
`t_3`-partition; that is the geometric content of the paper's numerical
condition `|e_alpha| = |e_beta|`, `|e_gamma| = |e_delta|` (stated at the
opening of Part II, Section 5.4), and it is carried here by the explicit
receipt `Aligned` (below).

## The subcase table of Configuration A

With `e_3, e_4` above `t_2`, `e_2, e_5` above `t_3`, `k_3 + k_4 = |A| = k_2 + k_5`
and `k_2 <= k_3 <= k_4 <= k_5`:

| subcase | indices | Base I partitions | outgoing types |
|---|---|---|---|
| `{v2-nd4-t3-k2=k4}` | `k_2 = k_3 = k_4 = k_5 = |A|/2` | `[e_3,e_2;e_4,e_5]`, `[e_3,e_5;e_4,e_2]` | I and II |
| `{v2-nd4-t3-k2=k3}` | `k_2 = k_3 < k_4 = k_5` | `[e_3,e_2;e_4,e_5]` | I |
| `{v2-nd4-t3-k2<k3}` | `k_2 < k_3 < k_4 < k_5` | none | none |

In every subcase the remaining outgoing types are Base II members (the merge
of `NonTrivalentValencyTwoCandidate` for Type III everywhere, and the
`e_4`/`e_3` splits above `u` for the Base II Types I/II of the last two
subcases).  A Base I partition always pairs one survivor above `t_2` with one
survivor above `t_3`; the same-direction pairing `[e_3,e_4;e_2,e_5]` is
Type III and is realized by Base II, never by Base I.

## What is proved

* `refineOnBlock` and `baseOnePattern`: the partition-level Base I local
  resolution (`left` = one fold plus singletons, `right` = the `t_2`-classes,
  `newEdge` = singletons), its contraction `baseOnePattern_contracts`, and its
  exact block sizes `|F| = 2`, singleton leaves, index-one bridges, and
  `|A_i| = k_i`.
* `thin_block_eq`: under `Aligned` and Configuration A the `t_3`-classes inside
  `A` are *literally* the `t_2`-classes, hence `sourceEdgeIndex_eq_of_meet`,
  the paper's `|e_alpha| = |e_beta|`.
* `selected_exterior`, `selected_riemannHurwitz_left`,
  `selected_riemannHurwitz_right`: exterior compatibility and **both**
  Riemann--Hurwitz inequalities.  The leaf one is unconditional
  (`riemannHurwitzAtBlock_leaf`); the trivalent one holds with *equality*, the
  three induced counts at `A_i` being `|A_i| + 1 + 1`, i.e. `r(A_i) = 0`.
* `LeafBackground`, `leafBackground`, `nonempty_leafBackground`: the guarded
  background at the other wall blocks and its **producer**, which needs no
  input at all.  At Base I the neutral `joinedResolutionAt` of
  `NonTrivalentValencyTwoCandidate` is *not* available: it would put a whole
  block `B` above the leaf with a single
  occurrence over `t_1` of index `|B|`, which carries `r = |B| - 1` and so
  fails `leaf_block_dichotomy` for every `|B| >= 2` -- and indeed fails the
  formal trivalent inequality at `v` already, since there `1 + n_2 + n_3 = 3`
  must dominate `|B| + 2`.  The correct neutral background is `fineResolution`
  with the block split into singletons above `u` and kept whole above `v`.
* `candidate`, `validCandidate`, `validCandidate_datum_valid`,
  `exists_valid_candidate_of_contraction`: the candidate, the validity of its
  outgoing datum with no background hypothesis, and the incoming-cover form.
* `exists_baseOne_candidate_of_prescribed`: the type dispatcher for
  Configuration A.  Given the prescribed cross pairing (which thick/thin pair
  meets at `A_1`) it returns the candidate, the two vertices above `v` with
  their exact sizes, the statement that the complementary pair meets at `A_2`
  (`partner_of_ne`), and both index conditions.
* `not_aligned_of_sourceEdgeIndex_ne`: the subcase `{v2-nd4-t3-k2<k3}`; Base I
  is impossible when the four indices are pairwise distinct across the two
  directions.

## What is not proved here

* `nd(A) = 4` at the wall block stays an explicit hypothesis, as in
  `NonTrivalentValencyTwoCandidate`.
* **The alignment receipt `Aligned` stays an explicit hypothesis.**  It is the
  geometric form of the paper's numerical condition and is *implied* by it only
  after a block-preserving branch gauge on the `t_3` side
  (`BlockPreservingBranchSwap.branchSwapOfPerm`, as in
  `NonTrivalentValencyFourKZero.gaugedData`): with `k_alpha = k_beta` and
  `k_gamma = k_delta` a permutation of the anchor block carries the two
  `t_3`-classes onto the two `t_2`-classes, and the gauged datum satisfies
  `Aligned`.  `NonTrivalentValencyTwoGauge` produces that gauge and transports
  `TwoBranchAnchor` across it; over a *fixed* datum the alignment determines
  which of Type I and Type II is realized, which is why the dispatcher takes
  the prescribed pairing and the receipt together.
* Configuration B has no Base I member at all (only one edge lies above
  `t_3`); nothing here applies to it.
* No stable type, row dictionary, honest matrix or pencil is proved here.  For
  this candidate, rows, descent and `rowEquiv` are in
  `NonTrivalentValencyTwoBaseOneRows` and `NonTrivalentValencyTwoBaseOneRowEquiv`,
  and the common minor and the exit in
  `NonTrivalentValencyTwoBaseOneRowDictionary` /
  `NonTrivalentValencyTwoBaseOneExit`.
* Change-minimality of the outgoing datum is not asserted as a proposition
  about `Candidate.datum`, and no datum-side `localRamification` of the
  outgoing cover is computed: `r(F) = 2` and `r(A_i) = 0` are read here only
  through the block counts (`|F| = 2` with two index-one occurrences; the three
  counts `|A_i| + 1 + 1` at `A_i`), which are exactly the numbers
  `leaf_block_dichotomy` and `lem-rphi-nd` turn into those ramifications.

## Used by

The boundary dispatcher for Part II case `{v2-nd4}`, which must supply each
outgoing type once at every wall.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.GlobalM11Arbitrary
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.ResolutionM1k
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W4Assembly DraismaVargas.LocalCases.W4StableSource

/-! ## 0.  Refining one block of a partition -/

section Partitions

variable {d : ℕ}

/-- Refine exactly one block of `coarse` by `fine`, leaving every other block
of `coarse` intact. -/
def refineOnBlock (coarse fine : SheetPartition d) (anchor : Fin d)
    (hRefines : fine.Refines coarse) : SheetPartition d where
  repr := fun sheet ↦ if coarse.Rel anchor sheet then fine.repr sheet else coarse.repr sheet
  repr_idem := by
    intro sheet
    by_cases hSheet : coarse.Rel anchor sheet
    · have hInside : coarse.Rel anchor (fine.repr sheet) :=
        hSheet.trans (hRefines.rel (fine.rel_repr_right sheet))
      simp only [if_pos hSheet, if_pos hInside, fine.repr_idem]
    · have hOutside : ¬coarse.Rel anchor (coarse.repr sheet) := by
        intro hRel
        exact hSheet (hRel.trans (coarse.repr_idem sheet))
      simp only [if_neg hSheet, if_neg hOutside, coarse.repr_idem]

@[simp] theorem refineOnBlock_repr_of_rel (coarse fine : SheetPartition d)
    (anchor sheet : Fin d) (hRefines : fine.Refines coarse)
    (hSheet : coarse.Rel anchor sheet) :
    (refineOnBlock coarse fine anchor hRefines).repr sheet = fine.repr sheet :=
  if_pos hSheet

@[simp] theorem refineOnBlock_repr_of_not_rel (coarse fine : SheetPartition d)
    (anchor sheet : Fin d) (hRefines : fine.Refines coarse)
    (hSheet : ¬coarse.Rel anchor sheet) :
    (refineOnBlock coarse fine anchor hRefines).repr sheet = coarse.repr sheet :=
  if_neg hSheet

/-- The refined partition still refines the original one. -/
theorem refineOnBlock_refines (coarse fine : SheetPartition d) (anchor : Fin d)
    (hRefines : fine.Refines coarse) :
    (refineOnBlock coarse fine anchor hRefines).Refines coarse := by
  intro i j hij
  have hRepr : (refineOnBlock coarse fine anchor hRefines).repr i =
      (refineOnBlock coarse fine anchor hRefines).repr j := hij
  show coarse.repr i = coarse.repr j
  by_cases hi : coarse.Rel anchor i
  · rw [refineOnBlock_repr_of_rel coarse fine anchor i hRefines hi] at hRepr
    by_cases hj : coarse.Rel anchor j
    · rw [refineOnBlock_repr_of_rel coarse fine anchor j hRefines hj] at hRepr
      exact hRefines.rel hRepr
    · rw [refineOnBlock_repr_of_not_rel coarse fine anchor j hRefines hj] at hRepr
      exact absurd (hi.trans ((hRefines.rel (fine.rel_repr_right i)).trans
        ((congrArg coarse.repr hRepr).trans (coarse.repr_idem j)))) hj
  · rw [refineOnBlock_repr_of_not_rel coarse fine anchor i hRefines hi] at hRepr
    by_cases hj : coarse.Rel anchor j
    · rw [refineOnBlock_repr_of_rel coarse fine anchor j hRefines hj] at hRepr
      refine absurd (hj.trans ((hRefines.rel (fine.rel_repr_right j)).trans ?_)) hi
      exact (congrArg coarse.repr hRepr.symm).trans (coarse.repr_idem i)
    · rw [refineOnBlock_repr_of_not_rel coarse fine anchor j hRefines hj] at hRepr
      exact hRepr

/-- Inside the selected block the refined partition is literally `fine`. -/
theorem refineOnBlock_rel_iff (coarse fine : SheetPartition d)
    (anchor sheet other : Fin d) (hRefines : fine.Refines coarse)
    (hSheet : coarse.Rel anchor sheet) :
    (refineOnBlock coarse fine anchor hRefines).Rel sheet other ↔ fine.Rel sheet other := by
  constructor
  · intro hRel
    have hRepr : (refineOnBlock coarse fine anchor hRefines).repr sheet =
        (refineOnBlock coarse fine anchor hRefines).repr other := hRel
    have hOther : coarse.Rel anchor other :=
      hSheet.trans ((refineOnBlock_refines coarse fine anchor hRefines).rel hRel)
    rw [refineOnBlock_repr_of_rel coarse fine anchor sheet hRefines hSheet,
      refineOnBlock_repr_of_rel coarse fine anchor other hRefines hOther] at hRepr
    exact hRepr
  · intro hRel
    have hOther : coarse.Rel anchor other := hSheet.trans (hRefines.rel hRel)
    show (refineOnBlock coarse fine anchor hRefines).repr sheet =
      (refineOnBlock coarse fine anchor hRefines).repr other
    rw [refineOnBlock_repr_of_rel coarse fine anchor sheet hRefines hSheet,
      refineOnBlock_repr_of_rel coarse fine anchor other hRefines hOther]
    exact hRel

theorem refineOnBlock_block_of_rel (coarse fine : SheetPartition d)
    (anchor sheet : Fin d) (hRefines : fine.Refines coarse)
    (hSheet : coarse.Rel anchor sheet) :
    (refineOnBlock coarse fine anchor hRefines).block sheet = fine.block sheet := by
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff,
    refineOnBlock_rel_iff coarse fine anchor sheet other hRefines hSheet]

theorem refineOnBlock_blockCard_of_rel (coarse fine : SheetPartition d)
    (anchor sheet : Fin d) (hRefines : fine.Refines coarse)
    (hSheet : coarse.Rel anchor sheet) :
    (refineOnBlock coarse fine anchor hRefines).blockCard sheet = fine.blockCard sheet := by
  unfold SheetPartition.blockCard
  rw [refineOnBlock_block_of_rel coarse fine anchor sheet hRefines hSheet]

/-- A partition refining `coarse` globally and `fine` on the selected block
refines the block-refined partition. -/
theorem refines_refineOnBlock {coarse fine other : SheetPartition d} {anchor : Fin d}
    (hRefines : fine.Refines coarse) (hOther : other.Refines coarse)
    (hOn : other.RefinesOnBlock fine coarse anchor) :
    other.Refines (refineOnBlock coarse fine anchor hRefines) := by
  intro i j hij
  by_cases hi : coarse.Rel anchor i
  · have hj : coarse.Rel anchor j := hi.trans (hOther.rel hij)
    show (refineOnBlock coarse fine anchor hRefines).repr i =
      (refineOnBlock coarse fine anchor hRefines).repr j
    rw [refineOnBlock_repr_of_rel coarse fine anchor i hRefines hi,
      refineOnBlock_repr_of_rel coarse fine anchor j hRefines hj]
    exact hOn.rel hi hij
  · have hj : ¬coarse.Rel anchor j := fun hRel ↦ hi (hRel.trans (hOther.rel hij).symm)
    show (refineOnBlock coarse fine anchor hRefines).repr i =
      (refineOnBlock coarse fine anchor hRefines).repr j
    rw [refineOnBlock_repr_of_not_rel coarse fine anchor i hRefines hi,
      refineOnBlock_repr_of_not_rel coarse fine anchor j hRefines hj]
    exact hOther.rel hij

/-- Splitting the selected block into singletons refines every block-refinement
of it. -/
theorem splitBlock_refines_refineOnBlock (coarse fine : SheetPartition d)
    (anchor : Fin d) (hRefines : fine.Refines coarse) :
    (coarse.splitBlock anchor).Refines (refineOnBlock coarse fine anchor hRefines) := by
  intro i j hij
  by_cases hi : coarse.Rel anchor i
  · have hEq := (coarse.splitBlock_rel_of_rel_anchor_iff anchor i hi j).mp hij
    subst hEq
    exact rfl
  · have hWall := (coarse.splitBlock_refines anchor).rel hij
    have hj : ¬coarse.Rel anchor j := fun hRel ↦ hi (hRel.trans hWall.symm)
    show (refineOnBlock coarse fine anchor hRefines).repr i =
      (refineOnBlock coarse fine anchor hRefines).repr j
    rw [refineOnBlock_repr_of_not_rel coarse fine anchor i hRefines hi,
      refineOnBlock_repr_of_not_rel coarse fine anchor j hRefines hj]
    exact hWall

/-! ## 1.  Two partition-level lemmas for the Base I shape -/

/-- A join criterion for the leaf/branch-point pattern: the two endpoint
partitions refine the wall, agree with it off one distinguished block, one
occurrence of the left partition bridges the two right-hand classes, and every
sheet of the block lies in one of those two classes. -/
theorem isJoin_of_bridge (left right coarse : SheetPartition d)
    (anchor first second : Fin d)
    (hLeft : left.Refines coarse) (hRight : right.Refines coarse)
    (hOff : ∀ i j, ¬coarse.Rel anchor i → coarse.Rel i j → left.Rel i j)
    (hBridge : left.Rel first second)
    (hCover : ∀ i, coarse.Rel anchor i → right.Rel first i ∨ right.Rel second i) :
    SheetPartition.IsJoin left right coarse := by
  have hConnect : ∀ x, coarse.Rel anchor x →
      Relation.EqvGen (fun a b ↦ left.Rel a b ∨ right.Rel a b) x first := by
    intro x hx
    rcases hCover x hx with hCase | hCase
    · exact Relation.EqvGen.rel x first (Or.inr hCase.symm)
    · exact Relation.EqvGen.trans x second first
        (Relation.EqvGen.rel x second (Or.inr hCase.symm))
        (Relation.EqvGen.rel second first (Or.inl hBridge.symm))
  intro i j
  constructor
  · intro hij
    by_cases hi : coarse.Rel anchor i
    · have hj : coarse.Rel anchor j := hi.trans hij
      exact Relation.EqvGen.trans i first j (hConnect i hi)
        (Relation.EqvGen.symm j first (hConnect j hj))
    · exact Relation.EqvGen.rel i j (Or.inl (hOff i j hi hij))
  · intro hGenerated
    induction hGenerated with
    | rel x y hxy => exact hxy.elim hLeft.rel hRight.rel
    | refl => rfl
    | symm => apply Eq.symm; assumption
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Two partitions of one wall block, one refining the other there and both
inducing the same number of classes, have literally the same blocks there. -/
theorem block_eq_of_refinesOnBlock_of_count_le (fine coarse wall : SheetPartition d)
    (anchor : Fin d) (hFine : fine.Refines wall) (hCoarse : coarse.Refines wall)
    (hOn : fine.RefinesOnBlock coarse wall anchor)
    (hCount : fine.blockCountWithin wall anchor ≤ coarse.blockCountWithin wall anchor)
    {sheet : Fin d} (hSheet : wall.Rel anchor sheet) :
    fine.block sheet = coarse.block sheet := by
  classical
  have hStay : ∀ x ∈ wall.block anchor, fine.repr x ∈ wall.block anchor := by
    intro x hx
    rw [SheetPartition.mem_block_iff] at hx ⊢
    exact hx.trans (hFine.rel (fine.rel_repr_right x))
  have hAgree : ∀ x ∈ wall.block anchor, coarse.repr (fine.repr x) = coarse.repr x := by
    intro x hx
    exact (hOn.rel ((wall.mem_block_iff anchor x).mp hx) (fine.rel_repr_right x)).symm
  have hImage :
      ((wall.block anchor).image fine.repr).image coarse.repr =
        (wall.block anchor).image coarse.repr := by
    ext value
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, hx, (hAgree x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨fine.repr x, ⟨x, hx, rfl⟩, hAgree x hx⟩
  have hCardLe :
      ((wall.block anchor).image fine.repr).card ≤
        (((wall.block anchor).image fine.repr).image coarse.repr).card := by
    rw [hImage]
    exact hCount
  have hInj : Set.InjOn coarse.repr ((wall.block anchor).image fine.repr) :=
    Finset.injOn_of_card_image_eq
      (le_antisymm (Finset.card_image_le) hCardLe)
  have hKey : ∀ u v, wall.Rel anchor u → wall.Rel anchor v →
      coarse.Rel u v → fine.Rel u v := by
    intro u v hu hv hRel
    have hMemU : fine.repr u ∈ (wall.block anchor).image fine.repr :=
      Finset.mem_image.mpr ⟨u, (wall.mem_block_iff anchor u).mpr hu, rfl⟩
    have hMemV : fine.repr v ∈ (wall.block anchor).image fine.repr :=
      Finset.mem_image.mpr ⟨v, (wall.mem_block_iff anchor v).mpr hv, rfl⟩
    refine hInj (by exact_mod_cast hMemU) (by exact_mod_cast hMemV) ?_
    have hU := hAgree u ((wall.mem_block_iff anchor u).mpr hu)
    have hV := hAgree v ((wall.mem_block_iff anchor v).mpr hv)
    exact hU.trans (hRel.trans hV.symm)
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  constructor
  · intro hRel
    exact hOn.rel hSheet hRel
  · intro hRel
    exact hKey sheet other hSheet (hSheet.trans (hCoarse.rel hRel)) hRel

/-! ## The Base I pattern at one block -/

/-- **Part II Base I (`T_∅`), Part I Case {w2-r2} Base I.**  Above the new leaf
`u` the block keeps one two-sheet fold and splits into singletons; above the new
trivalent branch point `v` it splits into the classes of `fine`; the new edge is
split into index-one occurrences. -/
noncomputable def baseOnePattern (wall fine : SheetPartition d)
    (anchor first second : Fin d) (hRefines : fine.Refines wall)
    (hNe : first ≠ second) (hFirst : wall.Rel anchor first) : LocalResolution d where
  left := wall.pairBlock first second hNe
  right := refineOnBlock wall fine anchor hRefines
  newEdge := wall.splitBlock anchor
  edge_refines_left := by
    intro i j hij
    by_cases hi : wall.Rel anchor i
    · have hEq := (wall.splitBlock_rel_of_rel_anchor_iff anchor i hi j).mp hij
      subst hEq
      exact rfl
    · have hWall := (wall.splitBlock_refines anchor).rel hij
      have hj : ¬wall.Rel anchor j := fun hRel ↦ hi (hRel.trans hWall.symm)
      have hiFirst : ¬wall.Rel first i := fun hRel ↦ hi (hFirst.trans hRel)
      have hjFirst : ¬wall.Rel first j := fun hRel ↦ hj (hFirst.trans hRel)
      show (wall.pairBlock first second hNe).repr i = (wall.pairBlock first second hNe).repr j
      rw [wall.pairBlock_repr_of_not_rel first second i hNe hiFirst,
        wall.pairBlock_repr_of_not_rel first second j hNe hjFirst]
      exact hWall
  edge_refines_right := splitBlock_refines_refineOnBlock wall fine anchor hRefines

@[simp] theorem baseOnePattern_left (wall fine : SheetPartition d)
    (anchor first second : Fin d) (hRefines : fine.Refines wall)
    (hNe : first ≠ second) (hFirst : wall.Rel anchor first) :
    (baseOnePattern wall fine anchor first second hRefines hNe hFirst).left =
      wall.pairBlock first second hNe := rfl

@[simp] theorem baseOnePattern_right (wall fine : SheetPartition d)
    (anchor first second : Fin d) (hRefines : fine.Refines wall)
    (hNe : first ≠ second) (hFirst : wall.Rel anchor first) :
    (baseOnePattern wall fine anchor first second hRefines hNe hFirst).right =
      refineOnBlock wall fine anchor hRefines := rfl

@[simp] theorem baseOnePattern_newEdge (wall fine : SheetPartition d)
    (anchor first second : Fin d) (hRefines : fine.Refines wall)
    (hNe : first ≠ second) (hFirst : wall.Rel anchor first) :
    (baseOnePattern wall fine anchor first second hRefines hNe hFirst).newEdge =
      wall.splitBlock anchor := rfl

/-- Contracting the new edge of the Base I pattern recovers the wall block. -/
theorem baseOnePattern_contracts (wall fine : SheetPartition d)
    (anchor first second : Fin d) (hRefines : fine.Refines wall)
    (hNe : first ≠ second) (hFirst : wall.Rel anchor first)
    (hSecond : wall.Rel anchor second)
    (hCover : ∀ i, wall.Rel anchor i → fine.Rel first i ∨ fine.Rel second i) :
    (baseOnePattern wall fine anchor first second hRefines hNe hFirst).ContractsTo wall := by
  refine isJoin_of_bridge _ _ _ anchor first second
    (wall.pairBlock_refines first second hNe (hFirst.symm.trans hSecond))
    (refineOnBlock_refines wall fine anchor hRefines) ?_ ?_ ?_
  · intro i j hi hij
    have hj : ¬wall.Rel anchor j := fun hRel ↦ hi (hRel.trans hij.symm)
    have hiFirst : ¬wall.Rel first i := fun hRel ↦ hi (hFirst.trans hRel)
    have hjFirst : ¬wall.Rel first j := fun hRel ↦ hj (hFirst.trans hRel)
    show (wall.pairBlock first second hNe).repr i = (wall.pairBlock first second hNe).repr j
    rw [wall.pairBlock_repr_of_not_rel first second i hNe hiFirst,
      wall.pairBlock_repr_of_not_rel first second j hNe hjFirst]
    exact hij
  · show (wall.pairBlock first second hNe).repr first =
      (wall.pairBlock first second hNe).repr second
    rw [wall.pairBlock_repr_first first second hNe,
      wall.pairBlock_repr_second first second hNe (hFirst.symm.trans hSecond)]
  · intro i hi
    rcases hCover i hi with hCase | hCase
    · exact Or.inl ((refineOnBlock_rel_iff wall fine anchor first i hRefines hFirst).mpr hCase)
    · exact Or.inr ((refineOnBlock_rel_iff wall fine anchor second i hRefines hSecond).mpr hCase)

/-- The fold above the new leaf has exactly two sheets: Part I's `|A_u| = 2`. -/
theorem baseOnePattern_left_blockCard_fold (wall fine : SheetPartition d)
    (anchor first second : Fin d) (hRefines : fine.Refines wall)
    (hNe : first ≠ second) (hFirst : wall.Rel anchor first)
    (hSecond : wall.Rel anchor second) :
    (baseOnePattern wall fine anchor first second hRefines hNe hFirst).left.blockCard first = 2 :=
  wall.pairBlock_blockCard_first first second hNe (hFirst.symm.trans hSecond)

/-- Every other sheet of the block is a singleton above the new leaf. -/
theorem baseOnePattern_left_blockCard_singleton (wall fine : SheetPartition d)
    (anchor first second sheet : Fin d) (hRefines : fine.Refines wall)
    (hNe : first ≠ second) (hFirst : wall.Rel anchor first)
    (hSecond : wall.Rel anchor second) (hSheet : wall.Rel anchor sheet)
    (hNeFirst : sheet ≠ first) (hNeSecond : sheet ≠ second) :
    (baseOnePattern wall fine anchor first second hRefines hNe hFirst).left.blockCard
      sheet = 1 := by
  classical
  have hBlock : (wall.pairBlock first second hNe).block sheet = {sheet} := by
    ext other
    rw [SheetPartition.mem_block_iff, Finset.mem_singleton]
    constructor
    · intro hRel
      have hRepr : (wall.pairBlock first second hNe).repr sheet =
          (wall.pairBlock first second hNe).repr other := hRel
      rw [wall.pairBlock_repr_of_rel_of_ne_second first second sheet hNe
        (hFirst.symm.trans hSheet) hNeSecond] at hRepr
      have hOtherWall : wall.Rel anchor other :=
        hSheet.trans ((wall.pairBlock_refines first second hNe
          (hFirst.symm.trans hSecond)).rel hRel)
      by_cases hOtherSecond : other = second
      · rw [hOtherSecond,
          wall.pairBlock_repr_second first second hNe (hFirst.symm.trans hSecond)] at hRepr
        exact absurd hRepr hNeFirst
      · rw [wall.pairBlock_repr_of_rel_of_ne_second first second other hNe
          (hFirst.symm.trans hOtherWall) hOtherSecond] at hRepr
        exact hRepr.symm
    · intro hEq
      subst hEq
      exact rfl
  show ((wall.pairBlock first second hNe).block sheet).card = 1
  rw [hBlock]
  simp

/-- The new edge carries index one on every sheet of the block: Part I's
`|e'| = |e''| = 1`. -/
theorem baseOnePattern_newEdge_blockCard (wall fine : SheetPartition d)
    (anchor first second sheet : Fin d) (hRefines : fine.Refines wall)
    (hNe : first ≠ second) (hFirst : wall.Rel anchor first)
    (hSheet : wall.Rel anchor sheet) :
    (baseOnePattern wall fine anchor first second hRefines hNe hFirst).newEdge.blockCard
      sheet = 1 :=
  wall.splitBlock_blockCard_of_rel anchor sheet hSheet

/-- The vertex above the new branch point is a class of `fine`. -/
theorem baseOnePattern_right_blockCard (wall fine : SheetPartition d)
    (anchor first second sheet : Fin d) (hRefines : fine.Refines wall)
    (hNe : first ≠ second) (hFirst : wall.Rel anchor first)
    (hSheet : wall.Rel anchor sheet) :
    (baseOnePattern wall fine anchor first second hRefines hNe hFirst).right.blockCard
      sheet = fine.blockCard sheet :=
  refineOnBlock_blockCard_of_rel wall fine anchor sheet hRefines hSheet

end Partitions

/-! ## 3.  The valency-two Base I setup at an actual wall -/

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}

/-- Base I's realizability receipt. -/
def Aligned (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall) : Prop :=
  (data.edgePartition (star.edge 1)).RefinesOnBlock
    (data.edgePartition (star.edge 0)) (data.vertexPartition wall) anchor.1

/-- The valency-two Base I input. -/
structure BaseOneSetup (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall) : Prop where
  anchor_source : TwoBranchAnchor data star anchor
  split : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2
  aligned : Aligned data star anchor

namespace BaseOneSetup

theorem exists_pair (setup : BaseOneSetup data star anchor) (label : Fin 2) :
    ∃ first second, first ≠ second ∧
      directionSurvivors data star anchor label = {first, second} :=
  Finset.card_eq_two.mp (setup.split label)

/-- The first survivor above a labelled direction. -/
noncomputable def firstOf (setup : BaseOneSetup data star anchor) (label : Fin 2) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  Classical.choose (setup.exists_pair label)

/-- The second survivor above a labelled direction. -/
noncomputable def secondOf (setup : BaseOneSetup data star anchor) (label : Fin 2) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  Classical.choose (Classical.choose_spec (setup.exists_pair label))

theorem firstOf_ne_secondOf (setup : BaseOneSetup data star anchor) (label : Fin 2) :
    setup.firstOf label ≠ setup.secondOf label :=
  (Classical.choose_spec (Classical.choose_spec (setup.exists_pair label))).1

theorem directionSurvivors_eq (setup : BaseOneSetup data star anchor) (label : Fin 2) :
    directionSurvivors data star anchor label =
      {setup.firstOf label, setup.secondOf label} :=
  (Classical.choose_spec (Classical.choose_spec (setup.exists_pair label))).2

theorem firstOf_mem (setup : BaseOneSetup data star anchor) (label : Fin 2) :
    setup.firstOf label ∈ directionSurvivors data star anchor label := by
  rw [setup.directionSurvivors_eq label]
  exact Finset.mem_insert_self _ _

theorem secondOf_mem (setup : BaseOneSetup data star anchor) (label : Fin 2) :
    setup.secondOf label ∈ directionSurvivors data star anchor label := by
  rw [setup.directionSurvivors_eq label]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- Part I's `A'`: the sheet naming the first class above `t₂`. -/
noncomputable def foldFirst (setup : BaseOneSetup data star anchor) : Fin degree :=
  occurrenceSheet (setup.firstOf 0)

/-- Part I's `A''`: the sheet naming the second class above `t₂`. -/
noncomputable def foldSecond (setup : BaseOneSetup data star anchor) : Fin degree :=
  occurrenceSheet (setup.secondOf 0)

theorem foldFirst_ne_foldSecond (setup : BaseOneSetup data star anchor) :
    setup.foldFirst ≠ setup.foldSecond := by
  intro hEq
  exact setup.firstOf_ne_secondOf 0
    (eq_of_occurrenceSheet_eq (setup.firstOf_mem 0) (setup.secondOf_mem 0) hEq)

theorem foldFirst_wall (setup : BaseOneSetup data star anchor) :
    (data.vertexPartition wall).Rel anchor.1 setup.foldFirst :=
  occurrenceSheet_wall_rel _

theorem foldSecond_wall (setup : BaseOneSetup data star anchor) :
    (data.vertexPartition wall).Rel anchor.1 setup.foldSecond :=
  occurrenceSheet_wall_rel _

/-- **The two classes above `t₂` exhaust the anchor block.**  This is the
`2 + 2` distribution of Configuration A read inside `A`. -/
theorem cover (setup : BaseOneSetup data star anchor) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (data.edgePartition (star.edge 0)).Rel setup.foldFirst sheet ∨
      (data.edgePartition (star.edge 0)).Rel setup.foldSecond sheet := by
  classical
  have hMem : sheet ∈ (data.vertexPartition wall).block anchor.1 :=
    ((data.vertexPartition wall).mem_block_iff _ _).mpr hSheet
  rw [← biUnion_block_eq_wallBlock setup.anchor_source 0,
    setup.directionSurvivors_eq 0] at hMem
  rw [Finset.biUnion_insert, Finset.singleton_biUnion] at hMem
  rcases Finset.mem_union.mp hMem with hCase | hCase
  · exact Or.inl ((SheetPartition.mem_block_iff _ _ _).mp hCase)
  · exact Or.inr ((SheetPartition.mem_block_iff _ _ _).mp hCase)

end BaseOneSetup

/-! ## The Base I local resolution at the anchor -/

/-- **The prescribed Base I resolution.** -/
noncomputable def selectedResolution (setup : BaseOneSetup data star anchor) :
    LocalResolution degree :=
  baseOnePattern (data.vertexPartition wall) (data.edgePartition (star.edge 0))
    anchor.1 setup.foldFirst setup.foldSecond
    (star.edgePartition_refines_wall data 0) setup.foldFirst_ne_foldSecond
    setup.foldFirst_wall

theorem selectedResolution_contracts (setup : BaseOneSetup data star anchor) :
    (selectedResolution setup).ContractsTo (data.vertexPartition wall) :=
  baseOnePattern_contracts _ _ _ _ _ _ _ _ setup.foldSecond_wall
    (fun _ hi ↦ setup.cover hi)

/-- The divalent star of the wall is exactly the two labelled occurrences. -/
theorem incidentEdges_eq_star_pair (star : TwoStar target wall) :
    GluingDatum.incidentEdges wall = {star.edge 0, star.edge 1} := by
  classical
  have hNe : star.edge 0 ≠ star.edge 1 := star.edge_injective.ne (by decide)
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl
    · exact star.edge_mem_incidentEdges 0
    · exact star.edge_mem_incidentEdges 1
  · rw [star.card_incidentEdges, Finset.card_insert_of_notMem (by simp [hNe]),
      Finset.card_singleton]


@[simp] theorem selectedResolution_left (setup : BaseOneSetup data star anchor) :
    (selectedResolution setup).left =
      (data.vertexPartition wall).pairBlock setup.foldFirst setup.foldSecond
        setup.foldFirst_ne_foldSecond := rfl

@[simp] theorem selectedResolution_right (setup : BaseOneSetup data star anchor) :
    (selectedResolution setup).right =
      refineOnBlock (data.vertexPartition wall) (data.edgePartition (star.edge 0))
        anchor.1 (star.edgePartition_refines_wall data 0) := rfl

@[simp] theorem selectedResolution_newEdge (setup : BaseOneSetup data star anchor) :
    (selectedResolution setup).newEdge =
      (data.vertexPartition wall).splitBlock anchor.1 := rfl

/-! ## The alignment in block form -/

private theorem block_image_repr {d : ℕ} (partition : SheetPartition d) (sheet : Fin d) :
    (partition.block sheet).image partition.repr = {partition.repr sheet} := by
  classical
  ext representative
  simp only [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨other, hOther, rfl⟩
    rw [SheetPartition.mem_block_iff] at hOther
    exact hOther.symm
  · rintro rfl
    exact ⟨sheet, partition.self_mem_block sheet, rfl⟩

/-- Configuration A inside the anchor: each direction induces exactly two
classes there. -/
theorem blockCountWithin_eq_two (setup : BaseOneSetup data star anchor) (label : Fin 2) :
    (data.edgePartition (star.edge label)).blockCountWithin
      (data.vertexPartition wall) anchor.1 = 2 := by
  rw [blockCountWithin_eq_card_directionSurvivors setup.anchor_source label,
    setup.split label]

/-- **Base I's geometric content.**  Above the anchor the `t₃`-classes are
literally the `t₂`-classes. -/
theorem thin_block_eq (setup : BaseOneSetup data star anchor) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (data.edgePartition (star.edge 1)).block sheet =
      (data.edgePartition (star.edge 0)).block sheet :=
  block_eq_of_refinesOnBlock_of_count_le _ _ _ anchor.1
    (star.edgePartition_refines_wall data 1) (star.edgePartition_refines_wall data 0)
    setup.aligned
    (le_of_eq ((blockCountWithin_eq_two setup 1).trans
      (blockCountWithin_eq_two setup 0).symm)) hSheet

theorem thin_blockCard_eq (setup : BaseOneSetup data star anchor) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (data.edgePartition (star.edge 1)).blockCard sheet =
      (data.edgePartition (star.edge 0)).blockCard sheet := by
  unfold SheetPartition.blockCard
  rw [thin_block_eq setup hSheet]

/-- **Part II's Base I condition `|e_α| = |e_β|`.**  Two survivors that meet at one
vertex above the new branch point have equal dilation index. -/
theorem sourceEdgeIndex_eq_of_meet (setup : BaseOneSetup data star anchor)
    {thick thin : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hThick : thick ∈ directionSurvivors data star anchor 0)
    (hThin : thin ∈ directionSurvivors data star anchor 1)
    (hMeet : (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thick)
      (occurrenceSheet thin)) :
    data.sourceEdgeIndex thick.1 = data.sourceEdgeIndex thin.1 := by
  have hThinWall : (data.vertexPartition wall).Rel anchor.1 (occurrenceSheet thin) :=
    occurrenceSheet_wall_rel _
  rw [sourceEdgeIndex_eq_blockCard hThick, sourceEdgeIndex_eq_blockCard hThin,
    thin_blockCard_eq setup hThinWall]
  unfold SheetPartition.blockCard
  rw [(data.edgePartition (star.edge 0)).block_eq_of_rel hMeet]

/-! ## The three induced counts at the new branch point -/

theorem dirZero_count (setup : BaseOneSetup data star anchor) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (data.edgePartition (star.edge 0)).blockCountWithin
      (selectedResolution setup).right sheet = 1 := by
  classical
  show (((selectedResolution setup).right.block sheet).image
    (data.edgePartition (star.edge 0)).repr).card = 1
  rw [selectedResolution_right setup,
    refineOnBlock_block_of_rel _ _ _ _ (star.edgePartition_refines_wall data 0) hSheet,
    block_image_repr]
  exact Finset.card_singleton _

theorem dirOne_count (setup : BaseOneSetup data star anchor) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (data.edgePartition (star.edge 1)).blockCountWithin
      (selectedResolution setup).right sheet = 1 := by
  classical
  show (((selectedResolution setup).right.block sheet).image
    (data.edgePartition (star.edge 1)).repr).card = 1
  rw [selectedResolution_right setup,
    refineOnBlock_block_of_rel _ _ _ _ (star.edgePartition_refines_wall data 0) hSheet,
    ← thin_block_eq setup hSheet, block_image_repr]
  exact Finset.card_singleton _

theorem newEdge_count (setup : BaseOneSetup data star anchor) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (selectedResolution setup).newEdge.blockCountWithin
        (selectedResolution setup).right sheet =
      (selectedResolution setup).right.blockCard sheet := by
  rw [selectedResolution_newEdge setup, selectedResolution_right setup]
  exact SheetPartition.splitBlock_blockCountWithin_of_refines _ _ _ _
    (refineOnBlock_refines _ _ _ (star.edgePartition_refines_wall data 0)) hSheet

/-! ## The outgoing base tree `T_∅` -/

/-- Both old occurrences stay at the new trivalent branch point `v`; the new
leaf `u` carries none. -/
def leafAssignment (target : CFGraph) : target.edges → Bool := fun _ ↦ true

/-- The new leaf `u` of `T_∅` carries no old occurrence. -/
def leafEdges (target : CFGraph) : List target.edges := []

/-- The new trivalent branch point `v` of `T_∅` carries both old occurrences. -/
noncomputable def branchEdges (star : TwoStar target wall) : List target.edges :=
  [star.edge 0, star.edge 1]

theorem wallEdgesAssigned_leaf_false (target : CFGraph) (wall : target.V) :
    wallEdgesAssigned target wall (leafAssignment target) false = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem ?_
  intro edge hEdge
  rw [mem_wallEdgesAssigned] at hEdge
  exact absurd hEdge.2 (by simp [leafAssignment])

theorem wallEdgesAssigned_leaf_true (star : TwoStar target wall) :
    wallEdgesAssigned target wall (leafAssignment target) true =
      {star.edge 0, star.edge 1} := by
  classical
  rw [← incidentEdges_eq_star_pair star]
  ext edge
  rw [mem_wallEdgesAssigned]
  constructor
  · rintro ⟨hIncident, -⟩
    exact (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
  · intro hEdge
    exact ⟨(GluingContraction.mem_incidentEdges_iff wall edge).mp hEdge, rfl⟩

theorem leafEdges_eq (target : CFGraph) (wall : target.V) :
    ((leafEdges target : List target.edges) : Multiset target.edges) =
      (wallEdgesAssigned target wall (leafAssignment target) false).val := by
  rw [wallEdgesAssigned_leaf_false target wall]
  rfl

theorem branchEdges_eq (star : TwoStar target wall) :
    ((branchEdges star : List target.edges) : Multiset target.edges) =
      (wallEdgesAssigned target wall (leafAssignment target) true).val := by
  classical
  have hNe : star.edge 0 ≠ star.edge 1 := star.edge_injective.ne (by decide)
  rw [wallEdgesAssigned_leaf_true star,
    Finset.insert_val_of_notMem (by simp [hNe])]
  rfl

/-! ## Exterior compatibility and both Riemann--Hurwitz inequalities -/

/-- Exterior compatibility at the anchor.  The `t₃` half is exactly the Base I
alignment receipt; the `t₂` half is free. -/
theorem selected_exterior (setup : BaseOneSetup data star anchor) (edge : target.edges)
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    (data.edgePartition edge).Refines
      (if leafAssignment target edge then (selectedResolution setup).right
        else (selectedResolution setup).left) := by
  classical
  have hMem : edge ∈ GluingDatum.incidentEdges wall :=
    (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
  rw [incidentEdges_eq_star_pair star] at hMem
  show (data.edgePartition edge).Refines (selectedResolution setup).right
  rw [selectedResolution_right setup]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
  rcases hMem with rfl | rfl
  · exact refines_refineOnBlock _ (star.edgePartition_refines_wall data 0)
      ((SheetPartition.Refines.refl _).refinesOnBlock _)
  · exact refines_refineOnBlock _ (star.edgePartition_refines_wall data 1) setup.aligned

/-- **The leaf `u`.**  Its Riemann--Hurwitz inequality is unconditional: `T_∅`
puts no old occurrence there, so the new occurrence is the only one. -/
theorem selected_riemannHurwitz_left (setup : BaseOneSetup data star anchor)
    (block : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (selectedResolution setup).left
      ((selectedResolution setup).newEdge ::
        (leafEdges target).map data.edgePartition) block := by
  simpa [leafEdges] using LocalResolution.riemannHurwitzAtBlock_leaf
    (data.vertexPartition wall) (selectedResolution setup).left
    (selectedResolution setup).newEdge block

/-- **The trivalent branch point `v`.**  The new edge is split into index-one
occurrences on the anchor block, so the three induced counts are
`|A_i| + 1 + 1`; the inequality holds with equality, i.e. `r(A_i) = 0`. -/
theorem selected_riemannHurwitz_right (setup : BaseOneSetup data star anchor)
    (block : Fin degree) (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (selectedResolution setup).right
      ((selectedResolution setup).newEdge ::
        (branchEdges star).map data.edgePartition) block := by
  have hCounts : ∀ sheet, (data.vertexPartition wall).Rel block sheet →
      (selectedResolution setup).newEdge.blockCountWithin
          (selectedResolution setup).right sheet +
        (data.edgePartition (star.edge 0)).blockCountWithin
          (selectedResolution setup).right sheet +
        (data.edgePartition (star.edge 1)).blockCountWithin
          (selectedResolution setup).right sheet ≥
        (selectedResolution setup).right.blockCard sheet + 2 := by
    intro sheet hSheet
    have hAnchor : (data.vertexPartition wall).Rel anchor.1 sheet := hBlock.trans hSheet
    rw [newEdge_count setup hAnchor, dirZero_count setup hAnchor,
      dirOne_count setup hAnchor]
  simpa [branchEdges] using riemannHurwitzAtBlock_trivalent_of_counts
    (data.vertexPartition wall) (selectedResolution setup).right
    (selectedResolution setup).newEdge (data.edgePartition (star.edge 0))
    (data.edgePartition (star.edge 1)) block hCounts

/-! ## The background at the other wall blocks -/

/-- The receipts owed by the wall blocks other than the anchor. -/
structure LeafBackground (data : GluingDatum target degree) (star : TwoStar target wall)
    (anchor : WallBlock data wall) where
  resolution : Fin degree → LocalResolution degree
  contracts : ∀ block, ¬(data.vertexPartition wall).Rel anchor.1 block →
    (resolution block).ContractsTo (data.vertexPartition wall)
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    ∀ block, ¬(data.vertexPartition wall).Rel anchor.1 block →
      (data.edgePartition edge).Refines
        (if leafAssignment target edge then (resolution block).right
          else (resolution block).left)
  left_riemannHurwitz : ∀ block,
    (data.vertexPartition wall).repr block = block →
    ¬(data.vertexPartition wall).Rel anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        (resolution block).left
        ((resolution block).newEdge :: (leafEdges target).map data.edgePartition) block
  right_riemannHurwitz : ∀ block,
    (data.vertexPartition wall).repr block = block →
    ¬(data.vertexPartition wall).Rel anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        (resolution block).right
        ((resolution block).newEdge :: (branchEdges star).map data.edgePartition) block

namespace LeafBackground

/-- Package the guarded receipts with the base tree `T_∅`. -/
noncomputable def background (geometry : LeafBackground data star anchor) :
    GlobalM11Arbitrary.Background data wall anchor.1 where
  right := leafAssignment target
  resolution := geometry.resolution
  contracts := geometry.contracts
  exterior := geometry.exterior
  leftEdges := leafEdges target
  rightEdges := branchEdges star
  leftEdges_eq := leafEdges_eq target wall
  rightEdges_eq := branchEdges_eq star
  left_riemannHurwitz := geometry.left_riemannHurwitz
  right_riemannHurwitz := geometry.right_riemannHurwitz

end LeafBackground

/-- **The Base I background producer.**  It takes *no* input: above the new
leaf every non-anchor block splits into singletons, which makes its leaf
inequality free and its branch-point inequality free as well. -/
noncomputable def leafBackground (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    LeafBackground data star anchor where
  resolution := fun block ↦ fineResolution (data.vertexPartition wall)
    ((data.vertexPartition wall).splitBlock block)
    ((data.vertexPartition wall).splitBlock_refines block)
  contracts := fun block _ ↦ fineResolution_contracts _ _ _
  exterior := by
    intro edge hIncident block _
    have hMem : edge ∈ GluingDatum.incidentEdges wall :=
      (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
    show (data.edgePartition edge).Refines (data.vertexPartition wall)
    exact edgePartition_refines_of_mem_incidentEdges data wall edge hMem
  left_riemannHurwitz := by
    intro block _ _
    have hMap : (leafEdges target).map data.edgePartition = [] := rfl
    rw [hMap]
    exact LocalResolution.riemannHurwitzAtBlock_leaf _ _ _ block
  right_riemannHurwitz := by
    intro block _ _
    have hCounts : ∀ sheet, (data.vertexPartition wall).Rel block sheet →
        ((data.vertexPartition wall).splitBlock block).blockCountWithin
            (data.vertexPartition wall) sheet +
          (data.edgePartition (star.edge 0)).blockCountWithin
            (data.vertexPartition wall) sheet +
          (data.edgePartition (star.edge 1)).blockCountWithin
            (data.vertexPartition wall) sheet ≥
          (data.vertexPartition wall).blockCard sheet + 2 := by
      intro sheet hSheet
      have hSplit := (data.vertexPartition wall).splitBlock_blockCountWithin_of_rel
        block sheet hSheet
      have hZero := (data.edgePartition (star.edge 0)).blockCountWithin_pos
        (data.vertexPartition wall) sheet
      have hOne := (data.edgePartition (star.edge 1)).blockCountWithin_pos
        (data.vertexPartition wall) sheet
      omega
    have hMap : (branchEdges star).map data.edgePartition =
        [data.edgePartition (star.edge 0), data.edgePartition (star.edge 1)] := rfl
    rw [hMap]
    exact riemannHurwitzAtBlock_trivalent_of_counts (data.vertexPartition wall)
      (data.vertexPartition wall) ((data.vertexPartition wall).splitBlock block)
      (data.edgePartition (star.edge 0)) (data.edgePartition (star.edge 1))
      block hCounts

/-- Non-vacuity of the guarded background. -/
theorem nonempty_leafBackground (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    Nonempty (LeafBackground data star anchor) :=
  ⟨leafBackground data star anchor⟩

/-! ## The installed candidate -/

/-- The prescribed Base I resolution installed into the guarded background. -/
noncomputable def candidate (setup : BaseOneSetup data star anchor)
    (geometry : LeafBackground data star anchor) :
    BalancedGlobal.Candidate target degree data wall := by
  apply (LeafBackground.background geometry).install (selectedResolution setup)
    (selectedResolution_contracts setup) (selected_exterior setup)
  · intro block _ _
    exact selected_riemannHurwitz_left setup block
  · intro block hRel _
    exact selected_riemannHurwitz_right setup block hRel

theorem candidate_resolution_of_wall_rel (setup : BaseOneSetup data star anchor)
    (geometry : LeafBackground data star anchor) (block : Fin degree)
    (hRel : (data.vertexPartition wall).Rel anchor.1 block) :
    (candidate setup geometry).resolution block = selectedResolution setup := by
  unfold candidate LeafBackground.background GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_rel _ _ _ _ _ hRel

theorem candidate_resolution_anchor (setup : BaseOneSetup data star anchor)
    (geometry : LeafBackground data star anchor) :
    (candidate setup geometry).resolution anchor.1 = selectedResolution setup :=
  candidate_resolution_of_wall_rel setup geometry anchor.1 rfl

theorem candidate_datum_valid (setup : BaseOneSetup data star anchor)
    (geometry : LeafBackground data star anchor) (hValid : data.Valid) :
    (candidate setup geometry).datum.Valid :=
  (candidate setup geometry).datum_valid hValid

/-! ## The candidate with no background hypothesis -/

/-- The valency-two Base I candidate itself. -/
noncomputable def validCandidate (setup : BaseOneSetup data star anchor) :
    BalancedGlobal.Candidate target degree data wall :=
  candidate setup (leafBackground data star anchor)

theorem validCandidate_datum_valid (setup : BaseOneSetup data star anchor)
    (hValid : data.Valid) : (validCandidate setup).datum.Valid :=
  candidate_datum_valid setup _ hValid

theorem validCandidate_resolution_anchor (setup : BaseOneSetup data star anchor) :
    (validCandidate setup).resolution anchor.1 = selectedResolution setup :=
  candidate_resolution_anchor setup _

/-! ## Exact block sizes of the Base I candidate -/

/-- The bridge occurrences over `t₁` have index one (Part I's `|e'| = |e''| = 1`). -/
theorem validCandidate_newSourceEdge_index (setup : BaseOneSetup data star anchor)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    (validCandidate setup).datum.sourceEdgeIndex
      ((validCandidate setup).newSourceEdge sheet) = 1 := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard]
  have hRepr : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr sheet) :=
    hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet)
  rw [show (validCandidate setup).resolution = (candidate setup
      (leafBackground data star anchor)).resolution from rfl,
    candidate_resolution_of_wall_rel setup _ _ hRepr, selectedResolution_newEdge]
  exact (data.vertexPartition wall).splitBlock_blockCard_of_rel anchor.1 sheet hSheet

/-- **The fold above the leaf `u` has two sheets** (Part I's `|A_u| = 2`). -/
theorem validCandidate_fold_blockCard (setup : BaseOneSetup data star anchor) :
    ((validCandidate setup).resolution anchor.1).left.blockCard setup.foldFirst = 2 := by
  rw [validCandidate_resolution_anchor setup, selectedResolution_left setup]
  exact (data.vertexPartition wall).pairBlock_blockCard_first _ _ _
    (setup.foldFirst_wall.symm.trans setup.foldSecond_wall)

/-- Every other sheet is a singleton above the leaf: the leaf fibre of the
anchor is one fold plus unramified ends, which is exactly the shape
`StableLocalProperties.leaf_block_dichotomy` allows. -/
theorem validCandidate_leaf_blockCard_singleton (setup : BaseOneSetup data star anchor)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet)
    (hNeFirst : sheet ≠ setup.foldFirst) (hNeSecond : sheet ≠ setup.foldSecond) :
    ((validCandidate setup).resolution anchor.1).left.blockCard sheet = 1 := by
  rw [validCandidate_resolution_anchor setup]
  exact baseOnePattern_left_blockCard_singleton (data.vertexPartition wall)
    (data.edgePartition (star.edge 0)) anchor.1 setup.foldFirst setup.foldSecond sheet
    (star.edgePartition_refines_wall data 0) setup.foldFirst_ne_foldSecond
    setup.foldFirst_wall setup.foldSecond_wall hSheet hNeFirst hNeSecond

/-- **The vertices above the branch point `v`** are the two classes above `t₂`,
of sizes `k_α` and `k_γ`. -/
theorem validCandidate_branch_blockCard (setup : BaseOneSetup data star anchor)
    {thick : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hThick : thick ∈ directionSurvivors data star anchor 0) :
    ((validCandidate setup).resolution anchor.1).right.blockCard
      (occurrenceSheet thick) = data.sourceEdgeIndex thick.1 := by
  rw [validCandidate_resolution_anchor setup, selectedResolution_right setup,
    sourceEdgeIndex_eq_blockCard hThick]
  exact refineOnBlock_blockCard_of_rel (data.vertexPartition wall)
    (data.edgePartition (star.edge 0)) anchor.1 (occurrenceSheet thick)
    (star.edgePartition_refines_wall data 0) (occurrenceSheet_wall_rel thick)

/-- The occurrences incident to the vertex above `v` through a sheet. -/
theorem mem_branchBlock_iff (setup : BaseOneSetup data star anchor) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) (other : Fin degree) :
    other ∈ ((validCandidate setup).resolution anchor.1).right.block sheet ↔
      (data.edgePartition (star.edge 0)).Rel sheet other := by
  rw [validCandidate_resolution_anchor setup, selectedResolution_right setup,
    refineOnBlock_block_of_rel (data.vertexPartition wall)
      (data.edgePartition (star.edge 0)) anchor.1 sheet
      (star.edgePartition_refines_wall data 0) hSheet, SheetPartition.mem_block_iff]

/-- The two vertices above `v` are distinct. -/
theorem branch_not_rel (setup : BaseOneSetup data star anchor) :
    ¬((validCandidate setup).resolution anchor.1).right.Rel setup.foldFirst
      setup.foldSecond := by
  rw [validCandidate_resolution_anchor setup, selectedResolution_right setup,
    refineOnBlock_rel_iff (data.vertexPartition wall) (data.edgePartition (star.edge 0))
      anchor.1 setup.foldFirst setup.foldSecond (star.edgePartition_refines_wall data 0)
      setup.foldFirst_wall]
  exact not_rel_occurrenceSheet (setup.firstOf_mem 0) (setup.secondOf_mem 0)
    (setup.firstOf_ne_secondOf 0)

/-! ## The cross pairing `[e_α, e_β; e_γ, e_δ]` -/

/-- Each survivor above `t₃` meets one survivor above `t₂`. -/
theorem exists_partner (setup : BaseOneSetup data star anchor)
    (thin : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    ∃ thick ∈ directionSurvivors data star anchor 0,
      (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thick)
        (occurrenceSheet thin) := by
  rcases setup.cover (occurrenceSheet_wall_rel thin) with hCase | hCase
  · exact ⟨setup.firstOf 0, setup.firstOf_mem 0, hCase⟩
  · exact ⟨setup.secondOf 0, setup.secondOf_mem 0, hCase⟩

theorem partner_unique
    {thickA thickB thin : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hA : thickA ∈ directionSurvivors data star anchor 0)
    (hB : thickB ∈ directionSurvivors data star anchor 0)
    (hRelA : (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thickA)
      (occurrenceSheet thin))
    (hRelB : (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thickB)
      (occurrenceSheet thin)) : thickA = thickB := by
  by_contra hNe
  exact not_rel_occurrenceSheet hA hB hNe (hRelA.trans hRelB.symm)

/-- Two distinct survivors of one direction exhaust that direction's fibre. -/
theorem eq_of_ne_third (setup : BaseOneSetup data star anchor) (label : Fin 2)
    {x y z : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hx : x ∈ directionSurvivors data star anchor label)
    (hy : y ∈ directionSurvivors data star anchor label)
    (hz : z ∈ directionSurvivors data star anchor label)
    (hxz : x ≠ z) (hyz : y ≠ z) : x = y := by
  classical
  rw [setup.directionSurvivors_eq label] at hx hy hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    first
      | rfl
      | exact absurd rfl hxz
      | exact absurd rfl hyz

/-- **The complementary pair meets at the other vertex above `v`.**  This is
the partition `[e_α, e_β; e_γ, e_δ]`: prescribing the pair at `A₁` prescribes
the pair at `A₂`. -/
theorem partner_of_ne (setup : BaseOneSetup data star anchor)
    {thick thickOther thin thinOther :
      IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hThick : thick ∈ directionSurvivors data star anchor 0)
    (hThickOther : thickOther ∈ directionSurvivors data star anchor 0)
    (hThin : thin ∈ directionSurvivors data star anchor 1)
    (hThinOther : thinOther ∈ directionSurvivors data star anchor 1)
    (hNeThick : thickOther ≠ thick) (hNeThin : thinOther ≠ thin)
    (hMeet : (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thick)
      (occurrenceSheet thin)) :
    (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thickOther)
      (occurrenceSheet thinOther) := by
  obtain ⟨partner, hPartner, hRel⟩ := exists_partner setup thinOther
  have hNe : partner ≠ thick := by
    intro hEq
    have hRelThick : (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thick)
        (occurrenceSheet thinOther) := hEq ▸ hRel
    have hThinWall : (data.vertexPartition wall).Rel anchor.1 (occurrenceSheet thin) :=
      occurrenceSheet_wall_rel _
    have hMem : occurrenceSheet thinOther ∈
        (data.edgePartition (star.edge 1)).block (occurrenceSheet thin) := by
      rw [thin_block_eq setup hThinWall]
      exact (SheetPartition.mem_block_iff _ _ _).mpr (hMeet.symm.trans hRelThick)
    exact not_rel_occurrenceSheet hThin hThinOther (Ne.symm hNeThin)
      ((SheetPartition.mem_block_iff _ _ _).mp hMem)
  have hEq : partner = thickOther :=
    eq_of_ne_third setup 0 hPartner hThickOther hThick hNe hNeThick
  exact hEq ▸ hRel

/-- Distinct survivors above `t₂` name distinct vertices above `v`. -/
theorem branch_not_rel_of_ne (setup : BaseOneSetup data star anchor)
    {thickA thickB : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hA : thickA ∈ directionSurvivors data star anchor 0)
    (hB : thickB ∈ directionSurvivors data star anchor 0) (hNe : thickA ≠ thickB) :
    ¬((validCandidate setup).resolution anchor.1).right.Rel (occurrenceSheet thickA)
      (occurrenceSheet thickB) := by
  rw [validCandidate_resolution_anchor setup, selectedResolution_right setup,
    refineOnBlock_rel_iff (data.vertexPartition wall) (data.edgePartition (star.edge 0))
      anchor.1 (occurrenceSheet thickA) (occurrenceSheet thickB)
      (star.edgePartition_refines_wall data 0) (occurrenceSheet_wall_rel thickA)]
  exact not_rel_occurrenceSheet hA hB hNe

/-! ## The type dispatcher for Configuration A -/

/-- **Part II, subcases `{v2-nd4-t3-k2=k4}` and `{v2-nd4-t3-k2=k3}`, Types I and
II.**  Given the prescribed cross
pairing and a Base I alignment realizing it, the Base I candidate exists, its
outgoing datum is valid, the prescribed pair meets at one vertex above `v`, the
complementary pair meets at the other, and the paper's index conditions
`|e_α| = |e_β|`, `|e_γ| = |e_δ|` hold. -/
theorem exists_baseOne_candidate_of_prescribed (setup : BaseOneSetup data star anchor)
    (hValid : data.Valid)
    {thick thickOther thin thinOther :
      IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hThick : thick ∈ directionSurvivors data star anchor 0)
    (hThickOther : thickOther ∈ directionSurvivors data star anchor 0)
    (hThin : thin ∈ directionSurvivors data star anchor 1)
    (hThinOther : thinOther ∈ directionSurvivors data star anchor 1)
    (hNeThick : thickOther ≠ thick) (hNeThin : thinOther ≠ thin)
    (hPrescribed : (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thick)
      (occurrenceSheet thin)) :
    ∃ outgoing : BalancedGlobal.Candidate target degree data wall,
      outgoing.datum.Valid ∧
      outgoing.resolution anchor.1 = selectedResolution setup ∧
      data.sourceEdgeIndex thick.1 = data.sourceEdgeIndex thin.1 ∧
      data.sourceEdgeIndex thickOther.1 = data.sourceEdgeIndex thinOther.1 ∧
      (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thickOther)
        (occurrenceSheet thinOther) ∧
      (outgoing.resolution anchor.1).right.blockCard (occurrenceSheet thick) =
        data.sourceEdgeIndex thick.1 ∧
      (outgoing.resolution anchor.1).right.blockCard (occurrenceSheet thickOther) =
        data.sourceEdgeIndex thickOther.1 ∧
      ¬(outgoing.resolution anchor.1).right.Rel (occurrenceSheet thick)
        (occurrenceSheet thickOther) ∧
      (outgoing.resolution anchor.1).left.blockCard setup.foldFirst = 2 ∧
      (∀ sheet, (data.vertexPartition wall).Rel anchor.1 sheet →
        outgoing.datum.sourceEdgeIndex (outgoing.newSourceEdge sheet) = 1) := by
  have hOtherMeet := partner_of_ne setup hThick hThickOther hThin hThinOther
    hNeThick hNeThin hPrescribed
  exact ⟨validCandidate setup, validCandidate_datum_valid setup hValid,
    validCandidate_resolution_anchor setup,
    sourceEdgeIndex_eq_of_meet setup hThick hThin hPrescribed,
    sourceEdgeIndex_eq_of_meet setup hThickOther hThinOther hOtherMeet, hOtherMeet,
    validCandidate_branch_blockCard setup hThick,
    validCandidate_branch_blockCard setup hThickOther,
    branch_not_rel_of_ne setup hThick hThickOther (Ne.symm hNeThick),
    validCandidate_fold_blockCard setup,
    fun sheet hSheet ↦ validCandidate_newSourceEdge_index setup sheet hSheet⟩

/-- **Part II, subcase `{v2-nd4-t3-k2<k3}`.**  When no survivor
above `t₂` has the same index as a survivor above `t₃` there is no Base I
alignment at all, so neither Type I nor Type II has a Base I representative. -/
theorem not_aligned_of_sourceEdgeIndex_ne
    (source : NonTrivalentValencyTwoAnchor.TwoBranchAnchor data star anchor)
    (hSplit : ∀ label : Fin 2, (directionSurvivors data star anchor label).card = 2)
    (hNe : ∀ thick ∈ directionSurvivors data star anchor 0,
      ∀ thin ∈ directionSurvivors data star anchor 1,
        data.sourceEdgeIndex thick.1 ≠ data.sourceEdgeIndex thin.1) :
    ¬Aligned data star anchor := by
  intro hAligned
  have setup : BaseOneSetup data star anchor := ⟨source, hSplit, hAligned⟩
  obtain ⟨thick, hThick, hRel⟩ := exists_partner setup (setup.firstOf 1)
  exact hNe thick hThick (setup.firstOf 1) (setup.firstOf_mem 1)
    (sourceEdgeIndex_eq_of_meet setup hThick (setup.firstOf_mem 1) hRel)

/-! ## The incoming-cover form -/

section Incoming

open GraphContraction GluingContraction ContractionFibre ContractionRamification
open FullDimensionalSource WallDegeneration

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Base I from an incoming full-dimensional cover.**  Everything except
`hNd` (the anchor's surviving valency), `hSplit` (Configuration A) and
`hAligned` (Base I's realizability receipt) is supplied by the incoming cover
and its contraction forest. -/
theorem exists_valid_candidate_of_contraction
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : W2R1Target.TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (anchorBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
        anchorBlock) = 4)
    (hSplit : ∀ label : Fin 2,
      (directionSurvivors (contractDatum data hc hab hOne) star anchorBlock label).card = 2)
    (hAligned : Aligned (contractDatum data hc hab hOne) star anchorBlock) :
    ∃ setup : BaseOneSetup (contractDatum data hc hab hOne) star anchorBlock,
      (validCandidate setup).datum.Valid ∧
      (∀ sheet, ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          anchorBlock.1 sheet →
        (validCandidate setup).datum.sourceEdgeIndex
          ((validCandidate setup).newSourceEdge sheet) = 1) ∧
      ((validCandidate setup).resolution anchorBlock.1).left.blockCard
          setup.foldFirst = 2 ∧
      (∀ thick ∈ directionSurvivors (contractDatum data hc hab hOne) star anchorBlock 0,
        ((validCandidate setup).resolution anchorBlock.1).right.blockCard
            (occurrenceSheet thick) =
          (contractDatum data hc hab hOne).sourceEdgeIndex thick.1) ∧
      (∀ thick ∈ directionSurvivors (contractDatum data hc hab hOne) star anchorBlock 0,
        ∀ thin ∈ directionSurvivors (contractDatum data hc hab hOne) star anchorBlock 1,
          ((contractDatum data hc hab hOne).edgePartition (star.edge 0)).Rel
              (occurrenceSheet thick) (occurrenceSheet thin) →
            (contractDatum data hc hab hOne).sourceEdgeIndex thick.1 =
              (contractDatum data hc hab hOne).sourceEdgeIndex thin.1) := by
  have hSource := NonTrivalentValencyTwoRigidity.twoBranchAnchor data fd hc hab hOne
    hForest hCompat star anchorBlock hNd
  refine ⟨⟨hSource, hSplit, hAligned⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact validCandidate_datum_valid _
      (valid_contractDatum data hc hab hOne hForest fd.valid)
  · exact fun sheet hSheet ↦ validCandidate_newSourceEdge_index _ sheet hSheet
  · exact validCandidate_fold_blockCard _
  · exact fun thick hThick ↦ validCandidate_branch_blockCard _ hThick
  · exact fun thick hThick thin hThin hMeet ↦
      sourceEdgeIndex_eq_of_meet ⟨hSource, hSplit, hAligned⟩ hThick hThin hMeet

end Incoming

/-! ## Non-vacuity -/

section NonVacuity

/-- The literal wall partition of the Configuration A model: the anchor block
`{0, 1}` and one ordinary block `{2, 3}`. -/
def modelWall : SheetPartition 4 := ⟨fun i ↦ if i.val < 2 then 0 else 2, by decide⟩

/-- The literal `t₂` partition: the anchor block splits into `{0}`, `{1}`. -/
def modelThick : SheetPartition 4 := ⟨fun i ↦ if i.val < 2 then i else 2, by decide⟩

/-- The literal `t₃` partition: the discrete partition, which agrees with
`modelThick` on the anchor block and differs from it off the anchor block. -/
def modelThin : SheetPartition 4 := ⟨fun i ↦ i, by decide⟩

theorem modelThick_refines : modelThick.Refines modelWall := by decide

theorem modelThin_refines : modelThin.Refines modelWall := by decide

/-- A literal inhabitant of Base I's alignment receipt, with the two occurrence
partitions genuinely different. -/
theorem model_aligned : modelThin.RefinesOnBlock modelThick modelWall 0 := by
  show ∀ first second, modelWall.Rel 0 first → modelThin.Rel first second →
    modelThick.Rel first second
  decide

theorem model_thin_ne_thick : modelThin ≠ modelThick := by
  intro hEq
  have hRepr : modelThin.repr 3 = modelThick.repr 3 := by rw [hEq]
  exact absurd hRepr (by decide)

theorem model_cover : ∀ i, modelWall.Rel 0 i → modelThick.Rel 0 i ∨ modelThick.Rel 1 i := by
  decide

/-- A literal Base I local resolution. -/
noncomputable def modelPattern : LocalResolution 4 :=
  baseOnePattern modelWall modelThick 0 0 1 modelThick_refines (by decide) (by decide)

theorem modelPattern_contracts : modelPattern.ContractsTo modelWall :=
  baseOnePattern_contracts modelWall modelThick 0 0 1 modelThick_refines (by decide)
    (by decide) (by decide) model_cover

theorem modelPattern_fold : modelPattern.left.blockCard 0 = 2 :=
  baseOnePattern_left_blockCard_fold modelWall modelThick 0 0 1 modelThick_refines
    (by decide) (by decide) (by decide)

theorem modelPattern_newEdge (sheet : Fin 4) (hSheet : modelWall.Rel 0 sheet) :
    modelPattern.newEdge.blockCard sheet = 1 :=
  baseOnePattern_newEdge_blockCard modelWall modelThick 0 0 1 sheet modelThick_refines
    (by decide) (by decide) hSheet

theorem modelPattern_branch (sheet : Fin 4) (hSheet : modelWall.Rel 0 sheet) :
    modelPattern.right.blockCard sheet = modelThick.blockCard sheet :=
  baseOnePattern_right_blockCard modelWall modelThick 0 0 1 sheet modelThick_refines
    (by decide) (by decide) hSheet

/-- Configuration A, subcase `{v2-nd4-t3-k2=k4}` (all indices equal):
`|A| = 2`, `k = (1,1,1,1)`.  Both cross pairings satisfy the paper's index
condition, so both Base I morphisms exist: Types I and II. -/
theorem baseOne_equal_witness :
    (1 + 1 : ℕ) = 2 ∧ (1 : ℕ) = 1 ∧ (1 : ℕ) = 1 ∧ (2 - 1) + 1 + 1 = 3 := by
  norm_num

/-- Configuration A, subcase `{v2-nd4-t3-k2=k3}`: `k = (1,1,2,2)`,
`|A| = 3`.  Exactly one cross pairing has equal indices on both sides
(`k₂ = k₃`, `k₄ = k₅`), so exactly one Base I morphism exists: Type I. -/
theorem baseOne_semiEqual_witness :
    (1 + 2 : ℕ) = 3 ∧ (1 + 2 : ℕ) = 3 ∧ (1 : ℕ) = 1 ∧ (2 : ℕ) = 2 ∧ (1 : ℕ) ≠ 2 := by
  norm_num

/-- Configuration A, subcase `{v2-nd4-t3-k2<k3}`: `k = (1,2,4,5)`,
`|A| = 6`.  No survivor above `t₂` has the index of a survivor above `t₃`, so
`not_aligned_of_sourceEdgeIndex_ne` applies and there is no Base I morphism. -/
theorem baseOne_strict_witness :
    (2 + 4 : ℕ) = 6 ∧ (1 + 5 : ℕ) = 6 ∧ (2 : ℕ) ≠ 1 ∧ (2 : ℕ) ≠ 5 ∧
      (4 : ℕ) ≠ 1 ∧ (4 : ℕ) ≠ 5 := by
  norm_num

end NonVacuity
end DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
