import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne

/-!
# Part II, valency two, Configuration A: the **Base II split** candidates

Source: Vargas, Part II (arXiv:2609.09109), Section 5.4, Configuration A of
Case {v2-nd4} (Case {v2-nd4-t3}): the Base II members of the subcases
`{v2-nd4-t3-k2=k3}` and `{v2-nd4-t3-k2<k3}` in which the class `e_4`, resp.
`e_3`, splits above `u` because `k_4 > k_2`, resp. `k_3 > k_2`, and the figures
of those subcases (`k_2 < k_3 < k_4`: Types I and II; `k_2 = k_3 < k_4`:
Type II).  Draisma--Vargas Part I (arXiv:1909.12924), Case {w2}, fixes the base
tree `T_2` (both new endpoints divalent).

`NonTrivalentValencyTwoCandidate` builds the Base II *merge* member and
`NonTrivalentValencyTwoBaseOne` the Base I members.  The prescribed-move walk
also needs the Base II *split* members: they are the only realization of a
cross pairing `{e_alpha, e_delta} | {e_beta, e_epsilon}` (one survivor of each
direction at each new vertex) when the two index equalities of Base I fail.
This module builds the split resolution at the partition level and installs it
into the subdivision background of `NonTrivalentValencyTwoCandidate`.

## The split picture

Above the anchor `A` with `t_thick`-classes `e_alpha, e_beta` and
`t_thin`-classes `e_delta, e_epsilon` (`k_delta < k_alpha`, and, after the
alignment gauge of `NonTrivalentValencyTwoSplitGauge`, `e_delta ⊆ e_alpha` as
sheet sets):

* above `u` (divalent, carrying `t_thick`): the vertices are the
  `t_thick`-classes themselves, `S = e_alpha` and the pass-through `P_u = e_beta`;
* above `v` (divalent, carrying `t_thin`): the vertices are the `t_thin`-classes,
  `A_v = e_epsilon` and the pass-through `P_v = e_delta`;
* above the new edge `t_1`: the common refinement
  `{e_delta, e_alpha ∖ e_delta, e_beta}` -- the piece `e_delta` (index
  `k_delta`) continuing to `e_delta`, the bridge `e_1 = e_alpha ∖ e_delta`
  (index `k_alpha - k_delta`, nonempty exactly when `k_alpha > k_delta`) joining
  `S` to `A_v`, and `e_beta` passing through to `A_v`.

The stable graph has `{h_alpha, h_delta}` at `S` and `{h_beta, h_epsilon}` at
`A_v`; with the paper's labels this is `H_{2,3}` (Type I) when `e_3` splits and
`H_{2,4}` (Type II) when `e_4` splits, as in Part II's subcase
`{v2-nd4-t3-k2=k3}`.  In its subcase `{v2-nd4-t3-k2<k3}` Part II attaches the
two type labels the other way round; the labels used here are read off the
stable graph.

## What is proved

* `meet`, `meet_rel_iff`, `meet_refines_left`, `meet_refines_right`,
  `meet_block`: the common refinement of two sheet partitions.
* `splitPattern`: the `LocalResolution` with `left = thick` and `right = thin`
  on the anchor block (the wall partition elsewhere) and `newEdge` their meet;
  `splitPattern_contracts`: it contracts to the wall as soon as one thick class
  meets both thin classes (`alpha`, `delta` in one thick class, in different
  thin classes, the block covered by those two thin classes);
  `splitPattern_newEdge_blockCard_piece`, `…_bridge`, `…_pass`: the exact
  new-edge class sizes `k_delta`, `k_alpha - k_delta`, `k_beta` under the
  sub-alignment `e_delta ⊆ e_alpha`.
* `SplitSetup`: the realizability hypothesis at an actual wall (Configuration A
  with the two chosen sheets `alpha`, `delta`), the split analogue of
  `NonTrivalentValencyTwoBaseOne.BaseOneSetup.aligned`.
* `selectedResolution` (unconditional), `selectedResolution_contracts`,
  `selected_exterior`, `selected_riemannHurwitz_left`,
  `selected_riemannHurwitz_right`: the resolution at the anchor and every
  receipt `GlobalM11Arbitrary.Background.install` asks for -- both endpoints
  are divalent, so both Riemann--Hurwitz inequalities are automatic exactly as
  in `NonTrivalentValencyTwoCandidate`.
* `candidate`, `validCandidate`, `validCandidate_datum_valid`,
  `validCandidate_resolution_anchor`, and the three block sizes at the
  anchor of the installed candidate.
* Non-vacuity of the pattern on a literal five-sheet model (`modelWall`,
  `modelThick`, `modelThin`: `k = (3, 2 | 2, 3)`, the piece of size `2`, the
  bridge of size `1`, the pass-through of size `2`).

## What is NOT proved -- the hypotheses that remain explicit

1. `SplitSetup` itself.  Its `sub` clause (`e_delta ⊆ e_alpha` as sheet sets) is
   the geometric form of the paper's `k_delta < k_alpha` and holds only after a
   block-preserving branch gauge on the `t_thin` side (the inclusion analogue of
   `NonTrivalentValencyTwoGauge.exists_alignment_perm`).
   `NonTrivalentValencyTwoSplitGauge` supplies it: the gauge
   `splitGaugedData` and its alignment `exists_splitAlignment_perm` need no
   hypothesis, and `splitSetup_gauged` produces `SplitSetup` from the single
   numerical hypothesis `k_delta < k_alpha` alone, so over the gauged datum it
   is not an extra hypothesis.
2. The orientation: this module puts the `thickEdge` of
   `NonTrivalentValencyTwoCandidate` at `u` (its `rightAssignment`), so it
   realizes the splits of a class over the thick direction; the mirror members
   (the thin direction at `u`) are the same construction over the reversed
   assignment, not built here.
   `NonTrivalentValencyTwoSplitGauge.thickDirection_eq_zero` shows
   Configuration A pins `thickDirection` to label `0`, so the mirror member is
   a `TwoStar` relabelling of this same construction rather than a new one.
3. No stable type, honest matrix, exit or tracking here: the rows and the row
   equivalence are in `NonTrivalentValencyTwoSplitRows` and
   `NonTrivalentValencyTwoSplitRowEquiv`, and the exit and tracking in
   `NonTrivalentValencyTwoSplitExit` and `NonTrivalentValencyTwoSplitTracks`.
4. `nd(A) = 4` is not used here at all; it enters through `TwoBranchAnchor` in
   the row modules, as for the merge and Base I members.

## Consumers

`NonTrivalentValencyTwoSplitGauge`, `NonTrivalentValencyTwoSplitRows` and
`NonTrivalentValencyTwoSplitRowEquiv`; through them, the valency-two move
dispatcher (`NonTrivalentValencyTwoDispatcher`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitCandidate

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.GlobalM11Arbitrary
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionM1k
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate.Prescribed
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne

/-! ## 1.  The common refinement of two sheet partitions -/

section Meet

variable {d : ℕ}

private theorem min'_congr {s t : Finset (Fin d)} (h : s = t) (hs : s.Nonempty) :
    s.min' hs = t.min' (h ▸ hs) := by
  subst h
  rfl

/-- The sheets related to `i` in both partitions. -/
private def meetBlock (first second : SheetPartition d) (i : Fin d) : Finset (Fin d) :=
  Finset.univ.filter fun j ↦ first.Rel i j ∧ second.Rel i j

private theorem mem_meetBlock (first second : SheetPartition d) (i j : Fin d) :
    j ∈ meetBlock first second i ↔ first.Rel i j ∧ second.Rel i j := by
  simp [meetBlock]

private theorem meetBlock_nonempty (first second : SheetPartition d) (i : Fin d) :
    (meetBlock first second i).Nonempty :=
  ⟨i, (mem_meetBlock first second i i).mpr ⟨rfl, rfl⟩⟩

private theorem meetBlock_eq_of_rel (first second : SheetPartition d) {i j : Fin d}
    (h₁ : first.Rel i j) (h₂ : second.Rel i j) :
    meetBlock first second i = meetBlock first second j := by
  ext k
  rw [mem_meetBlock, mem_meetBlock]
  constructor
  · rintro ⟨hf, hs⟩
    exact ⟨h₁.symm.trans hf, h₂.symm.trans hs⟩
  · rintro ⟨hf, hs⟩
    exact ⟨h₁.trans hf, h₂.trans hs⟩

/-- **The common refinement** of two sheet partitions: two sheets are related
when they are related in both. -/
def meet (first second : SheetPartition d) : SheetPartition d where
  repr := fun i ↦ (meetBlock first second i).min' (meetBlock_nonempty first second i)
  repr_idem := by
    intro i
    have hMem := Finset.min'_mem (meetBlock first second i) (meetBlock_nonempty first second i)
    rw [mem_meetBlock] at hMem
    exact (min'_congr (meetBlock_eq_of_rel first second hMem.1 hMem.2).symm _)

theorem meet_rel_iff (first second : SheetPartition d) (i j : Fin d) :
    (meet first second).Rel i j ↔ first.Rel i j ∧ second.Rel i j := by
  constructor
  · intro h
    have hi := Finset.min'_mem (meetBlock first second i) (meetBlock_nonempty first second i)
    have hj := Finset.min'_mem (meetBlock first second j) (meetBlock_nonempty first second j)
    have hEq : (meetBlock first second i).min' (meetBlock_nonempty first second i) =
        (meetBlock first second j).min' (meetBlock_nonempty first second j) := h
    rw [hEq] at hi
    rw [mem_meetBlock] at hi hj
    exact ⟨hi.1.trans hj.1.symm, hi.2.trans hj.2.symm⟩
  · rintro ⟨hf, hs⟩
    exact min'_congr (meetBlock_eq_of_rel first second hf hs) (meetBlock_nonempty first second i)

theorem meet_refines_left (first second : SheetPartition d) :
    (meet first second).Refines first :=
  fun _ _ h ↦ ((meet_rel_iff first second _ _).mp h).1

theorem meet_refines_right (first second : SheetPartition d) :
    (meet first second).Refines second :=
  fun _ _ h ↦ ((meet_rel_iff first second _ _).mp h).2

theorem meet_block (first second : SheetPartition d) (i : Fin d) :
    (meet first second).block i = first.block i ∩ second.block i := by
  ext j
  rw [Finset.mem_inter, SheetPartition.mem_block_iff, SheetPartition.mem_block_iff,
    SheetPartition.mem_block_iff, meet_rel_iff]

end Meet

/-! ## 2.  The split pattern at one block -/

section Pattern

variable {d : ℕ}

/-- **Part II Base II, the split member.**  Above the
divalent `u` the anchor block splits into the `thick` classes, above the divalent
`v` into the `thin` classes, and above the new edge into their common
refinement; every other block of the wall is left whole on both sides. -/
noncomputable def splitPattern (wall thick thin : SheetPartition d) (anchor : Fin d)
    (hThick : thick.Refines wall) (hThin : thin.Refines wall) : LocalResolution d where
  left := refineOnBlock wall thick anchor hThick
  right := refineOnBlock wall thin anchor hThin
  newEdge := refineOnBlock wall (meet thick thin) anchor
    ((meet_refines_left thick thin).trans hThick)
  edge_refines_left :=
    refines_refineOnBlock hThick
      (refineOnBlock_refines wall (meet thick thin) anchor _)
      (fun _ _ hFirst hRel ↦ (meet_refines_left thick thin).rel
        ((refineOnBlock_rel_iff wall (meet thick thin) anchor _ _ _ hFirst).mp hRel))
  edge_refines_right :=
    refines_refineOnBlock hThin
      (refineOnBlock_refines wall (meet thick thin) anchor _)
      (fun _ _ hFirst hRel ↦ (meet_refines_right thick thin).rel
        ((refineOnBlock_rel_iff wall (meet thick thin) anchor _ _ _ hFirst).mp hRel))

variable (wall thick thin : SheetPartition d) (anchor : Fin d)
  (hThick : thick.Refines wall) (hThin : thin.Refines wall)

@[simp] theorem splitPattern_left :
    (splitPattern wall thick thin anchor hThick hThin).left =
      refineOnBlock wall thick anchor hThick := rfl

@[simp] theorem splitPattern_right :
    (splitPattern wall thick thin anchor hThick hThin).right =
      refineOnBlock wall thin anchor hThin := rfl

@[simp] theorem splitPattern_newEdge :
    (splitPattern wall thick thin anchor hThick hThin).newEdge =
      refineOnBlock wall (meet thick thin) anchor
        ((meet_refines_left thick thin).trans hThick) := rfl

/-- **Contracting the new edge recovers the wall block** as soon as one thick
class (that of `alpha` and `delta`) meets both thin classes (those of `delta`
and `alpha`), which cover the block. -/
theorem splitPattern_contracts {alpha delta : Fin d}
    (hAlpha : wall.Rel anchor alpha) (hSame : thick.Rel alpha delta)
    (hCover : ∀ i, wall.Rel anchor i → thin.Rel delta i ∨ thin.Rel alpha i) :
    (splitPattern wall thick thin anchor hThick hThin).ContractsTo wall := by
  have hDelta : wall.Rel anchor delta := hAlpha.trans (hThick.rel hSame)
  refine isJoin_of_bridge _ _ _ anchor alpha delta
    (refineOnBlock_refines wall thick anchor hThick)
    (refineOnBlock_refines wall thin anchor hThin) ?_ ?_ ?_
  · intro i j hi hij
    have hj : ¬wall.Rel anchor j := fun hRel ↦ hi (hRel.trans hij.symm)
    show (refineOnBlock wall thick anchor hThick).repr i =
      (refineOnBlock wall thick anchor hThick).repr j
    rw [refineOnBlock_repr_of_not_rel wall thick anchor i hThick hi,
      refineOnBlock_repr_of_not_rel wall thick anchor j hThick hj]
    exact hij
  · exact (refineOnBlock_rel_iff wall thick anchor alpha delta hThick hAlpha).mpr hSame
  · intro i hi
    rcases hCover i hi with hCase | hCase
    · exact Or.inr ((refineOnBlock_rel_iff wall thin anchor delta i hThin hDelta).mpr hCase)
    · exact Or.inl ((refineOnBlock_rel_iff wall thin anchor alpha i hThin hAlpha).mpr hCase)

/-- On the anchor block the `u`-side vertices are the thick classes. -/
theorem splitPattern_left_blockCard {sheet : Fin d} (hSheet : wall.Rel anchor sheet) :
    (splitPattern wall thick thin anchor hThick hThin).left.blockCard sheet =
      thick.blockCard sheet :=
  refineOnBlock_blockCard_of_rel wall thick anchor sheet hThick hSheet

/-- On the anchor block the `v`-side vertices are the thin classes. -/
theorem splitPattern_right_blockCard {sheet : Fin d} (hSheet : wall.Rel anchor sheet) :
    (splitPattern wall thick thin anchor hThick hThin).right.blockCard sheet =
      thin.blockCard sheet :=
  refineOnBlock_blockCard_of_rel wall thin anchor sheet hThin hSheet

/-- On the anchor block a new-edge class is the intersection of a thick and a
thin class. -/
theorem splitPattern_newEdge_block {sheet : Fin d} (hSheet : wall.Rel anchor sheet) :
    (splitPattern wall thick thin anchor hThick hThin).newEdge.block sheet =
      thick.block sheet ∩ thin.block sheet := by
  rw [splitPattern_newEdge, refineOnBlock_block_of_rel wall (meet thick thin) anchor sheet _
    hSheet, meet_block]

/-- **The piece.**  Under the sub-alignment `e_delta ⊆ e_alpha` the new-edge
class of `delta` is the whole thin class `e_delta`, of index `k_delta`. -/
theorem splitPattern_newEdge_blockCard_piece {alpha delta : Fin d}
    (hDelta : wall.Rel anchor delta) (hSame : thick.Rel alpha delta)
    (hSub : thin.block delta ⊆ thick.block alpha) :
    (splitPattern wall thick thin anchor hThick hThin).newEdge.blockCard delta =
      thin.blockCard delta := by
  unfold SheetPartition.blockCard
  rw [splitPattern_newEdge_block wall thick thin anchor hThick hThin hDelta,
    thick.block_eq_of_rel hSame.symm]
  congr 1
  exact Finset.inter_eq_right.mpr hSub

/-- **The bridge.**  The new-edge class of `alpha` is `e_alpha ∖ e_delta`, of index
`k_alpha - k_delta`. -/
theorem splitPattern_newEdge_blockCard_bridge {alpha delta : Fin d}
    (hAlpha : wall.Rel anchor alpha)
    (hSub : thin.block delta ⊆ thick.block alpha) (hNot : ¬thin.Rel alpha delta)
    (hCover : ∀ i, wall.Rel anchor i → thin.Rel delta i ∨ thin.Rel alpha i) :
    (splitPattern wall thick thin anchor hThick hThin).newEdge.blockCard alpha =
      thick.blockCard alpha - thin.blockCard delta := by
  classical
  unfold SheetPartition.blockCard
  rw [splitPattern_newEdge_block wall thick thin anchor hThick hThin hAlpha]
  have hEq : thick.block alpha ∩ thin.block alpha = thick.block alpha \ thin.block delta := by
    ext x
    rw [Finset.mem_inter, Finset.mem_sdiff, SheetPartition.mem_block_iff,
      SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨hx, hxa⟩
      exact ⟨hx, fun hxd ↦ hNot (hxa.trans hxd.symm)⟩
    · rintro ⟨hx, hxd⟩
      refine ⟨hx, ?_⟩
      rcases hCover x (hAlpha.trans (hThick.rel hx)) with hCase | hCase
      · exact absurd hCase hxd
      · exact hCase
  rw [hEq, Finset.card_sdiff, Finset.inter_eq_left.mpr hSub]

/-- **The pass-through.**  A thick class other than `e_alpha` is a whole new-edge
class, of index `k_beta`. -/
theorem splitPattern_newEdge_blockCard_pass {alpha delta beta : Fin d}
    (hBeta : wall.Rel anchor beta)
    (hSub : thin.block delta ⊆ thick.block alpha) (hNe : ¬thick.Rel alpha beta)
    (hCover : ∀ i, wall.Rel anchor i → thin.Rel delta i ∨ thin.Rel alpha i) :
    (splitPattern wall thick thin anchor hThick hThin).newEdge.blockCard beta =
      thick.blockCard beta := by
  unfold SheetPartition.blockCard
  rw [splitPattern_newEdge_block wall thick thin anchor hThick hThin hBeta]
  congr 1
  refine Finset.inter_eq_left.mpr ?_
  have hKey : ∀ x, thick.Rel beta x → thin.Rel alpha x := by
    intro x hx
    rcases hCover x (hBeta.trans (hThick.rel hx)) with hCase | hCase
    · exfalso
      have hxa : x ∈ thick.block alpha :=
        hSub ((SheetPartition.mem_block_iff _ _ _).mpr hCase)
      rw [SheetPartition.mem_block_iff] at hxa
      exact hNe (hxa.trans hx.symm)
    · exact hCase
  intro x hx
  rw [SheetPartition.mem_block_iff] at hx ⊢
  exact (hKey beta rfl).symm.trans (hKey x hx)

end Pattern

/-! ## 3.  Non-vacuity of the pattern on a literal model

Five sheets, one wall block; thick classes `{0,1,2} | {3,4}` (`k_alpha = 3`,
`k_beta = 2`), thin classes `{0,1} | {2,3,4}` (`k_delta = 2 ⊆ e_alpha`,
`k_epsilon = 3`); `alpha = 2`, `delta = 0`.  The new-edge classes are the piece
`{0,1}`, the bridge `{2}` and the pass-through `{3,4}`. -/

section Model

def modelWall : SheetPartition 5 := ⟨fun _ ↦ 0, by decide⟩

def modelThick : SheetPartition 5 := ⟨fun i ↦ if i.val < 3 then 0 else 3, by decide⟩

def modelThin : SheetPartition 5 := ⟨fun i ↦ if i.val < 2 then 0 else 2, by decide⟩

theorem modelThick_refines : modelThick.Refines modelWall := by decide

theorem modelThin_refines : modelThin.Refines modelWall := by decide

/-- The model pattern contracts to the wall block. -/
theorem model_contracts :
    (splitPattern modelWall modelThick modelThin 0 modelThick_refines
      modelThin_refines).ContractsTo modelWall :=
  splitPattern_contracts modelWall modelThick modelThin 0 modelThick_refines modelThin_refines
    (alpha := 2) (delta := 0) (by decide) (by decide) (by decide)

/-- The three new-edge class sizes of the model: piece `2`, bridge `1`,
pass-through `2`. -/
theorem model_sizes :
    (splitPattern modelWall modelThick modelThin 0 modelThick_refines
        modelThin_refines).newEdge.blockCard 0 = 2 ∧
      (splitPattern modelWall modelThick modelThin 0 modelThick_refines
        modelThin_refines).newEdge.blockCard 2 = 1 ∧
      (splitPattern modelWall modelThick modelThin 0 modelThick_refines
        modelThin_refines).newEdge.blockCard 3 = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [splitPattern_newEdge_blockCard_piece modelWall modelThick modelThin 0 modelThick_refines
      modelThin_refines (alpha := 2) (delta := 0) (by decide) (by decide) (by decide)]
    decide
  · rw [splitPattern_newEdge_blockCard_bridge modelWall modelThick modelThin 0
      modelThick_refines modelThin_refines (alpha := 2) (delta := 0) (by decide) (by decide)
      (by decide) (by decide)]
    decide
  · rw [splitPattern_newEdge_blockCard_pass modelWall modelThick modelThin 0
      modelThick_refines modelThin_refines (alpha := 2) (delta := 0) (beta := 3) (by decide)
      (by decide) (by decide) (by decide)]
    decide

end Model

/-! ## 4.  The split setup at an actual wall, and the installed candidate -/

section Wall

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable (data : GluingDatum target degree) (star : TwoStar target wall)
  (anchor : WallBlock data wall)

/-- **The split realizability receipt.**  `alpha` and `delta` are two sheets of
the anchor block in one class of the thick direction (the class `e_alpha` that
splits) and in different classes of the thin direction, `e_delta` being
contained in `e_alpha` (the sub-alignment produced by the gauge of
`NonTrivalentValencyTwoSplitGauge`), and the two thin classes of `alpha` and
`delta` cover the block
(Configuration A).  Strictness `k_delta < k_alpha` is the statement that `alpha`
itself lies outside `e_delta`, which `not_thin` records. -/
structure SplitSetup (alpha delta : Fin degree) : Prop where
  alpha_wall : (data.vertexPartition wall).Rel anchor.1 alpha
  same_thick : (data.edgePartition (thickEdge data star anchor)).Rel alpha delta
  sub : (data.edgePartition (thinEdge data star anchor)).block delta ⊆
    (data.edgePartition (thickEdge data star anchor)).block alpha
  not_thin : ¬(data.edgePartition (thinEdge data star anchor)).Rel alpha delta
  cover : ∀ i, (data.vertexPartition wall).Rel anchor.1 i →
    (data.edgePartition (thinEdge data star anchor)).Rel delta i ∨
      (data.edgePartition (thinEdge data star anchor)).Rel alpha i

theorem thickEdge_refines_wall :
    (data.edgePartition (thickEdge data star anchor)).Refines (data.vertexPartition wall) :=
  star.edgePartition_refines_wall data _

theorem thinEdge_refines_wall :
    (data.edgePartition (thinEdge data star anchor)).Refines (data.vertexPartition wall) :=
  star.edgePartition_refines_wall data _

/-- **The split resolution at the anchor**, with the thick direction at `u` and
the thin direction at `v` (the `rightAssignment` of
`NonTrivalentValencyTwoCandidate`).  It is defined for
every datum; the receipt `SplitSetup` is needed only for contraction and for
the block sizes. -/
noncomputable def selectedResolution : LocalResolution degree :=
  splitPattern (data.vertexPartition wall) (data.edgePartition (thickEdge data star anchor))
    (data.edgePartition (thinEdge data star anchor)) anchor.1
    (thickEdge_refines_wall data star anchor) (thinEdge_refines_wall data star anchor)

variable {data star anchor}

theorem selectedResolution_contracts {alpha delta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta) :
    (selectedResolution data star anchor).ContractsTo (data.vertexPartition wall) :=
  splitPattern_contracts _ _ _ _ _ _ setup.alpha_wall setup.same_thick setup.cover

/-- Exterior compatibility with both old occurrences at the wall: each direction's
partition refines its own side, since that side *is* that partition on the
anchor block and the wall partition elsewhere. -/
theorem selected_exterior (edge : target.edges)
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    (data.edgePartition edge).Refines
      (if rightAssignment data star anchor edge then (selectedResolution data star anchor).right
        else (selectedResolution data star anchor).left) := by
  classical
  have hMem : edge ∈ GluingDatum.incidentEdges wall :=
    (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
  by_cases hEdge : edge = thickEdge data star anchor
  · subst hEdge
    rw [rightAssignment_thick data star anchor, if_neg (by simp)]
    exact refines_refineOnBlock (thickEdge_refines_wall data star anchor)
      (thickEdge_refines_wall data star anchor) ((SheetPartition.Refines.refl _).refinesOnBlock _)
  · rw [rightAssignment_of_ne data star anchor hEdge, if_pos rfl]
    rw [incidentEdges_eq_pair data star anchor] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with hThick | hThin
    · exact absurd hThick hEdge
    · subst hThin
      exact refines_refineOnBlock (thinEdge_refines_wall data star anchor)
        (thinEdge_refines_wall data star anchor) ((SheetPartition.Refines.refl _).refinesOnBlock _)

/-- The endpoint `u` is divalent, so its Riemann--Hurwitz inequality is automatic
(the argument of `NonTrivalentValencyTwoCandidate`, verbatim). -/
theorem selected_riemannHurwitz_left (block : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (selectedResolution data star anchor).left
      ((selectedResolution data star anchor).newEdge ::
        (leftEdges data star anchor).map data.edgePartition) block := by
  simpa [leftEdges] using riemannHurwitzAtBlock_divalent (data.vertexPartition wall)
    (selectedResolution data star anchor).left (selectedResolution data star anchor).newEdge
    (data.edgePartition (thickEdge data star anchor)) block

/-- The endpoint `v` is divalent as well. -/
theorem selected_riemannHurwitz_right (block : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (selectedResolution data star anchor).right
      ((selectedResolution data star anchor).newEdge ::
        (rightEdges data star anchor).map data.edgePartition) block := by
  simpa [rightEdges] using riemannHurwitzAtBlock_divalent (data.vertexPartition wall)
    (selectedResolution data star anchor).right (selectedResolution data star anchor).newEdge
    (data.edgePartition (thinEdge data star anchor)) block

/-- The split resolution installed into the guarded subdivision background of
`NonTrivalentValencyTwoCandidate`. -/
noncomputable def candidate {alpha delta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta)
    (geometry : SubdivisionBackground data star anchor) :
    BalancedGlobal.Candidate target degree data wall := by
  apply (SubdivisionBackground.background geometry).install
    (selectedResolution data star anchor) (selectedResolution_contracts setup)
    selected_exterior
  · intro block _ _
    exact selected_riemannHurwitz_left block
  · intro block _ _
    exact selected_riemannHurwitz_right block

theorem candidate_datum_valid {alpha delta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta)
    (geometry : SubdivisionBackground data star anchor) (hValid : data.Valid) :
    (candidate setup geometry).datum.Valid :=
  (candidate setup geometry).datum_valid hValid

theorem candidate_resolution_of_wall_rel {alpha delta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta)
    (geometry : SubdivisionBackground data star anchor) (block : Fin degree)
    (hRel : (data.vertexPartition wall).Rel anchor.1 block) :
    (candidate setup geometry).resolution block = selectedResolution data star anchor := by
  unfold candidate SubdivisionBackground.background GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_rel _ _ _ _ _ hRel

/-- **The split candidate**, over the hypothesis-free background of
`NonTrivalentValencyTwoCandidate`. -/
noncomputable def validCandidate {alpha delta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta) :
    BalancedGlobal.Candidate target degree data wall :=
  candidate setup (subdivisionBackground data star anchor)

theorem validCandidate_datum_valid {alpha delta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta) (hValid : data.Valid) :
    (validCandidate setup).datum.Valid :=
  candidate_datum_valid setup _ hValid

theorem validCandidate_resolution_anchor {alpha delta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta) :
    (validCandidate setup).resolution anchor.1 = selectedResolution data star anchor :=
  candidate_resolution_of_wall_rel setup _ anchor.1 rfl

/-- The piece over the new edge has the index of `e_delta`. -/
theorem validCandidate_newEdge_blockCard_piece {alpha delta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta) :
    ((validCandidate setup).resolution anchor.1).newEdge.blockCard delta =
      (data.edgePartition (thinEdge data star anchor)).blockCard delta := by
  rw [validCandidate_resolution_anchor]
  exact splitPattern_newEdge_blockCard_piece _ _ _ _ _ _
    (setup.alpha_wall.trans ((thickEdge_refines_wall data star anchor).rel setup.same_thick))
    setup.same_thick setup.sub

/-- The bridge over the new edge has index `k_alpha - k_delta`. -/
theorem validCandidate_newEdge_blockCard_bridge {alpha delta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta) :
    ((validCandidate setup).resolution anchor.1).newEdge.blockCard alpha =
      (data.edgePartition (thickEdge data star anchor)).blockCard alpha -
        (data.edgePartition (thinEdge data star anchor)).blockCard delta := by
  rw [validCandidate_resolution_anchor]
  exact splitPattern_newEdge_blockCard_bridge _ _ _ _ _ _ setup.alpha_wall setup.sub
    setup.not_thin setup.cover

/-- Every other thick class passes through the new edge whole. -/
theorem validCandidate_newEdge_blockCard_pass {alpha delta beta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta)
    (hBeta : (data.vertexPartition wall).Rel anchor.1 beta)
    (hNe : ¬(data.edgePartition (thickEdge data star anchor)).Rel alpha beta) :
    ((validCandidate setup).resolution anchor.1).newEdge.blockCard beta =
      (data.edgePartition (thickEdge data star anchor)).blockCard beta := by
  rw [validCandidate_resolution_anchor]
  exact splitPattern_newEdge_blockCard_pass _ _ _ _ _ _ hBeta setup.sub hNe setup.cover

/-- The `u`-side vertices of the split candidate are the thick classes and the
`v`-side vertices the thin classes. -/
theorem validCandidate_endpoint_blockCard {alpha delta : Fin degree}
    (setup : SplitSetup data star anchor alpha delta) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel anchor.1 sheet) :
    ((validCandidate setup).resolution anchor.1).left.blockCard sheet =
        (data.edgePartition (thickEdge data star anchor)).blockCard sheet ∧
      ((validCandidate setup).resolution anchor.1).right.blockCard sheet =
        (data.edgePartition (thinEdge data star anchor)).blockCard sheet := by
  rw [validCandidate_resolution_anchor]
  exact ⟨splitPattern_left_blockCard _ _ _ _ _ _ hSheet,
    splitPattern_right_blockCard _ _ _ _ _ _ hSheet⟩

end Wall

end DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitCandidate
