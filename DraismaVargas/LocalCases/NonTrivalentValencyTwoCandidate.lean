import DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
import DraismaVargas.LocalCases.NonTrivalentValencyTwoRigidity

/-!
# Part II, valency two: the prescribed candidate of case `{v2-nd4}`

Source: Vargas, Part II (arXiv:2609.09109), Section 5.4 (valency-2 limits),
with Draisma--Vargas Part I (arXiv:1909.12924), Case {w2}, fixing the two base
trees.

## Which choice the existence route needs

At a divalent wall `w0` with target occurrences `t2`, `t3` the anchor `A` has
`r0(A) = 4 - val w0 = 2` and four surviving occurrences
(`NonTrivalentValencyTwoAnchor.TwoBranchAnchor`), distributed `2+2`
(Configuration A, `{v2-nd4-t3}`) or `3+1` (Configuration B, `{v2-nd4-t2}`).
Part I, Case {w2}, lists the two trees contracting to `T0`: `T_empty` with
`val u = 1`, `val v = 3`, and `T_2` with `val u = val v = 2`.  So Part II's
Base I (`T_empty`) is the leaf/trivalent expansion and Base II
(`T_2`) is the *subdivision* of the divalent wall into two divalent endpoints,
which is the expansion `W2R1Target.TwoStar` supplies.  (The parenthetical
descriptions of the two trees at the start of Part II, Section 5.4 differ from
Part I's; this library follows Part I.)

Only Base II is needed, and only its *merge* member.

* Base II makes **both** new target endpoints divalent, so **both** endpoint
  Riemann--Hurwitz inequalities are automatic
  (`ResolutionM1k.riemannHurwitzAtBlock_divalent`), for every local resolution
  and every wall block at once.  Base I would put a trivalent endpoint carrying
  both old occurrences, and is in addition available only under the paper's
  numerical condition `|e_a| = |e_b|`, `|e_c| = |e_d|`, which fails
  outright in subcase `{v2-nd4-t3-k2<k3}` and in all of Configuration B.
* Inside Base II the paper's members are, in Configuration A, one *merge*
  morphism in each of the subcases `{v2-nd4-t3-k2=k4}`, `{v2-nd4-t3-k2=k3}` and
  `{v2-nd4-t3-k2<k3}` (Type III in the last two) and, in the subcases with a
  strict index, one or two *split* morphisms conditioned on `k_4 > k_2` or
  `k_3 > k_2`; in Configuration B they are the three ways to merge two of the
  three classes above `t_2`.  A merge is available in every subcase of both
  configurations, and it is the member built here.  The split members and every
  Base I member are needed only to count the morphisms, not for existence.

## The construction

Let `t_thick` be a target occurrence carrying at least two survivors -- either
one in Configuration A, the tripled one in Configuration B -- and let
`e_first`, `e_second` be two of its survivors.  Which two is **data**: it is
the structure `Prescribed.Selection` (two distinct survivors of the thick
direction), the valency-two analogue of the valency-four
`NonTrivalentValencyFourKZero.PrescribedPairing`'s `pairing : Fin 3`.  In
Configuration B (`3 + 1`) Base II has three merge members, one per
choice of pair, and a *prescribed* Whitehead move picks one of them; with the
pair hidden inside a `Classical.choose` no statement downstream could name it.
`Prescribed.Selection.default source` is a choice-made instance, and
`Prescribed.Selection.nonempty` is the non-vacuity witness.  The outgoing
target puts
`t_thick` at the divalent endpoint `u` and the other occurrence `t_thin` at the
divalent endpoint `v`.  The local resolution at `A` merges the two selected
classes and changes nothing else:

* `finePartition` is `data.edgePartition t_thick` with the blocks of `e_first`
  and `e_second` joined (`SheetPartition.mergeBlocks`).  No branch gauge is
  used: two distinct survivors above one target occurrence are already disjoint
  blocks of one edge partition, so the merged class is their honest union, of
  size exactly `k_first + k_second`.
* `selectedResolution = fineResolution (vertexPartition wall) finePartition`:
  the `u`-side carries the merged partition and the `v`-side keeps the whole old
  wall block, so `|A_v| = |A|`.

In Configuration A the thick direction has exactly two survivors of index sum
`|A|`, so the merged class is all of `A` and the bridge is a single occurrence
of index `|A|` (`selectedSheets_card_eq_blockCard_of_two`).  In Configuration B
the bridge occurrence through the selected representative has index
`k_first + k_second` and the remaining survivor's class is a second, divalent
occurrence above the new edge.  In both cases the *stable* effect on the source
is a Whitehead resolution of the four-valent `A`: the two selected survivors
`e_first`, `e_second` meet the new trivalent vertex over `u`, and the other two
survivors meet the new trivalent vertex `A_v = A` over `v`.  In Configuration A
that is exactly the split by target direction; in Configuration B the third
thick survivor reaches `A_v` through a divalent subdivision point over `u`.

## What is proved

* `Prescribed.Selection`, `Selection.default`, `Selection.nonempty`: the
  prescribed merged pair as a parameter, its choice-made instance and its
  non-vacuity.
* `selectedSheets`, `finePartition`, `selectedResolution`: the local resolution
  at `A`, its contraction and its exact endpoint sizes.
* `blockCountWithin_eq_card_directionSurvivors`: inside `A` the classes above a
  target occurrence are *exactly* its survivors -- no dangling singleton
  survives inside `A`, because each direction's survivor index sum is already
  `|A|` (`TwoBranchAnchor.direction_index_sum`).
* `selected_riemannHurwitz_left` / `selected_riemannHurwitz_right`: both
  endpoint Riemann--Hurwitz inequalities, automatic at a subdivided wall.
  `left_endpoint_thick_blockCount` / `right_endpoint_blockCount` record the
  exact counts behind them: the new vertex over `u` through the selected
  representative and the new vertex `A_v = A` over `v` each see exactly three
  occurrences, so each carries local ramification `3 - 2 = 1`, which is the
  anchor's share of Part II's change-minimality `ch(u) = ch(v) = 1` at a
  divalent target vertex; the
  `v`-side count uses `k_2 + k_3 + k_4 + k_5 = 2|A|` through the per-direction
  sums `TwoBranchAnchor.direction_index_sum`.
* `SubdivisionBackground`, `candidate`, `subdivisionBackground`: the guarded
  background of the rigid blocks and its **producer**, which needs *no*
  hypothesis at all -- not `data.Valid`, not a census, not `nd <= 3` off the
  anchor: at a subdivided divalent wall the neutral joined resolution
  discharges every guarded receipt, because both endpoints are divalent.
* `validCandidate`, `validCandidate_datum_valid` and
  `exists_valid_candidate_of_contraction`: the candidate and the validity of
  its outgoing datum, stated from an incoming full-dimensional cover and its
  contraction forest.

## What is NOT proved

* `nd(A) = 4` at the wall block is an explicit hypothesis throughout;
  `NonTrivalentAnchorValency` produces it from the wall metric.
* No stable type, row dictionary, honest matrix or pencil: those follow in
  `NonTrivalentValencyTwoRows` and the modules after it.
* Change-minimality of the outgoing datum is not asserted as a proposition
  about `Candidate.datum`; only the block counts it is computed from are
  proved here.

## Consumers

The boundary dispatcher for Part II, Case {v2-nd4}
(`NonTrivalentValencyTwoDispatcher`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.GlobalM11Arbitrary
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.ResolutionM1k
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.W2R1Target
open W4Assembly W4StableSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-! ## 0.  Two generic facts about joining two blocks of a partition -/

section MergeBlocks

variable {d : ℕ}

/-- Joining two blocks only coarsens: the original partition refines the
merged one. -/
theorem refines_mergeBlocks (partition : SheetPartition d) (first extra : Fin d)
    (hSeparate : ¬partition.Rel first extra) :
    partition.Refines (partition.mergeBlocks first extra hSeparate) := by
  intro i j hRel
  by_cases hCase : partition.Rel first i ∨ partition.Rel extra i
  · have hj : partition.Rel first j ∨ partition.Rel extra j := by
      rcases hCase with h | h
      · exact Or.inl (h.trans hRel)
      · exact Or.inr (h.trans hRel)
    have hi := (partition.mergeBlocks_rel_first_iff first extra i hSeparate).mpr hCase
    have hjj := (partition.mergeBlocks_rel_first_iff first extra j hSeparate).mpr hj
    exact hi.symm.trans hjj
  · obtain ⟨hNotFirst, hNotExtra⟩ := not_or.mp hCase
    have hBlock := partition.mergeBlocks_block_of_separate first extra i hSeparate
      (fun h ↦ hNotFirst h.symm) (fun h ↦ hNotExtra h.symm)
    have hMem : j ∈ partition.block i :=
      (partition.mem_block_iff i j).mpr hRel
    rw [← hBlock] at hMem
    exact ((partition.mergeBlocks first extra hSeparate).mem_block_iff i j).mp hMem

/-- Joining two blocks that already lie in one coarse block keeps the
refinement. -/
theorem mergeBlocks_refines (partition coarse : SheetPartition d)
    (first extra : Fin d) (hSeparate : ¬partition.Rel first extra)
    (hRefines : partition.Refines coarse) (hCoarse : coarse.Rel first extra) :
    (partition.mergeBlocks first extra hSeparate).Refines coarse := by
  intro i j hRel
  by_cases hCase : partition.Rel first i ∨ partition.Rel extra i
  · have hi := (partition.mergeBlocks_rel_first_iff first extra i hSeparate).mpr hCase
    have hjRel : (partition.mergeBlocks first extra hSeparate).Rel first j :=
      hi.trans hRel
    have hj := (partition.mergeBlocks_rel_first_iff first extra j hSeparate).mp hjRel
    have hci : coarse.Rel first i := by
      rcases hCase with h | h
      · exact hRefines.rel h
      · exact hCoarse.trans (hRefines.rel h)
    have hcj : coarse.Rel first j := by
      rcases hj with h | h
      · exact hRefines.rel h
      · exact hCoarse.trans (hRefines.rel h)
    exact hci.symm.trans hcj
  · obtain ⟨hNotFirst, hNotExtra⟩ := not_or.mp hCase
    have hBlock := partition.mergeBlocks_block_of_separate first extra i hSeparate
      (fun h ↦ hNotFirst h.symm) (fun h ↦ hNotExtra h.symm)
    have hMem : j ∈ (partition.mergeBlocks first extra hSeparate).block i :=
      ((partition.mergeBlocks first extra hSeparate).mem_block_iff i j).mpr hRel
    rw [hBlock] at hMem
    exact hRefines.rel ((partition.mem_block_iff i j).mp hMem)

end MergeBlocks

/-! ## 1.  Occurrence notation at the divalent wall -/

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}

/-- The sheet named by an incident source occurrence. -/
def occurrenceSheet {vertex : data.SourceVertex}
    (edge : IncidentSourceEdge data vertex) : Fin degree := edge.1.1.2

theorem occurrenceSheet_wall_rel
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    (data.vertexPartition wall).Rel anchor.1 (occurrenceSheet edge) := by
  have hIncident := (incident_wallBlock_sourceVertex_iff data anchor edge.1).mp edge.2
  have hRepr : (data.vertexPartition wall).repr (occurrenceSheet edge) = anchor.1 :=
    congrArg Subtype.val hIncident.2
  unfold SheetPartition.Rel
  rw [hRepr]
  exact anchor.2

/-- A survivor of a named direction lies above that target occurrence. -/
theorem survivor_target {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    edge.1.1.1 = star.edge label :=
  ((mem_directionSurvivors data star anchor label edge).mp hEdge).2

/-- Its sheet is the canonical representative of its own class. -/
theorem survivor_repr {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    (data.edgePartition (star.edge label)).repr (occurrenceSheet edge) =
      occurrenceSheet edge := by
  have h := edge.1.2
  rw [survivor_target hEdge] at h
  exact h

/-- Its dilation index is the cardinality of its class. -/
theorem sourceEdgeIndex_eq_blockCard {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    data.sourceEdgeIndex edge.1 =
      (data.edgePartition (star.edge label)).blockCard (occurrenceSheet edge) := by
  unfold GluingDatum.sourceEdgeIndex occurrenceSheet
  rw [survivor_target hEdge]

/-- Distinct survivors of one direction name distinct classes: this is why no
branch gauge is needed at a divalent wall. -/
theorem not_rel_occurrenceSheet {label : Fin 2}
    {first second : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hFirst : first ∈ directionSurvivors data star anchor label)
    (hSecond : second ∈ directionSurvivors data star anchor label)
    (hNe : first ≠ second) :
    ¬(data.edgePartition (star.edge label)).Rel
      (occurrenceSheet first) (occurrenceSheet second) := by
  intro hRel
  apply hNe
  have hFirstRepr := survivor_repr hFirst
  have hSecondRepr := survivor_repr hSecond
  unfold SheetPartition.Rel at hRel
  rw [hFirstRepr, hSecondRepr] at hRel
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rw [survivor_target hFirst, survivor_target hSecond]
  · exact hRel

/-- Distinct survivors of one direction name distinct sheets. -/
theorem eq_of_occurrenceSheet_eq {label : Fin 2}
    {first second : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hFirst : first ∈ directionSurvivors data star anchor label)
    (hSecond : second ∈ directionSurvivors data star anchor label)
    (hEq : occurrenceSheet first = occurrenceSheet second) : first = second := by
  by_contra hNe
  exact not_rel_occurrenceSheet hFirst hSecond hNe (by
    unfold SheetPartition.Rel
    rw [hEq])

/-- Every class of a direction inside the anchor lies inside the anchor's wall
block. -/
theorem block_subset_wallBlock (label : Fin 2)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    (data.edgePartition (star.edge label)).block (occurrenceSheet edge) ⊆
      (data.vertexPartition wall).block anchor.1 := by
  intro sheet hSheet
  rw [SheetPartition.mem_block_iff] at hSheet
  refine ((data.vertexPartition wall).mem_block_iff _ _).mpr ?_
  exact (occurrenceSheet_wall_rel edge).trans
    ((star.edgePartition_refines_wall data label).rel hSheet)

/-! ## 2.  Inside the anchor, a direction is exactly its survivors -/

/-- The surviving classes of one direction cover the whole anchor block: their
cardinalities already sum to `|A|` by `TwoBranchAnchor.direction_index_sum`, so
no dangling singleton is left over. -/
theorem biUnion_block_eq_wallBlock (source : TwoBranchAnchor data star anchor)
    (label : Fin 2) :
    ((directionSurvivors data star anchor label).biUnion fun edge ↦
        (data.edgePartition (star.edge label)).block (occurrenceSheet edge)) =
      (data.vertexPartition wall).block anchor.1 := by
  classical
  have hSubset :
      ((directionSurvivors data star anchor label).biUnion fun edge ↦
          (data.edgePartition (star.edge label)).block (occurrenceSheet edge)) ⊆
        (data.vertexPartition wall).block anchor.1 := by
    intro sheet hSheet
    obtain ⟨edge, hEdge, hMem⟩ := Finset.mem_biUnion.mp hSheet
    exact block_subset_wallBlock label edge hMem
  have hPairwise : ∀ first ∈ directionSurvivors data star anchor label,
      ∀ second ∈ directionSurvivors data star anchor label, first ≠ second →
      Disjoint ((data.edgePartition (star.edge label)).block (occurrenceSheet first))
        ((data.edgePartition (star.edge label)).block (occurrenceSheet second)) := by
    intro first hFirst second hSecond hNe
    refine Finset.disjoint_left.mpr ?_
    intro sheet hIn hOut
    rw [SheetPartition.mem_block_iff] at hIn hOut
    exact not_rel_occurrenceSheet hFirst hSecond hNe (hIn.trans hOut.symm)
  have hCard :
      ((directionSurvivors data star anchor label).biUnion fun edge ↦
          (data.edgePartition (star.edge label)).block (occurrenceSheet edge)).card =
        (data.vertexPartition wall).blockCard anchor.1 := by
    rw [Finset.card_biUnion hPairwise]
    have hSum := source.direction_index_sum label
    have hCast : ((∑ edge ∈ directionSurvivors data star anchor label,
        (data.edgePartition (star.edge label)).blockCard (occurrenceSheet edge) : ℕ) : ℤ) =
        ((data.vertexPartition wall).blockCard anchor.1 : ℤ) := by
      push_cast
      rw [← hSum]
      apply Finset.sum_congr rfl
      intro edge hEdge
      rw [sourceEdgeIndex_eq_blockCard hEdge]
    exact_mod_cast hCast
  exact Finset.eq_of_subset_of_card_le hSubset (le_of_eq hCard.symm)

/-- **The exact induced count.**  Inside the anchor block the classes above a
target occurrence are exactly its surviving occurrences. -/
theorem blockCountWithin_eq_card_directionSurvivors
    (source : TwoBranchAnchor data star anchor) (label : Fin 2) :
    (data.edgePartition (star.edge label)).blockCountWithin
        (data.vertexPartition wall) anchor.1 =
      (directionSurvivors data star anchor label).card := by
  classical
  have hImage :
      ((data.vertexPartition wall).block anchor.1).image
          (data.edgePartition (star.edge label)).repr =
        (directionSurvivors data star anchor label).image occurrenceSheet := by
    rw [← biUnion_block_eq_wallBlock source label]
    ext representative
    constructor
    · intro hMem
      obtain ⟨sheet, hSheet, rfl⟩ := Finset.mem_image.mp hMem
      obtain ⟨edge, hEdge, hBlock⟩ := Finset.mem_biUnion.mp hSheet
      refine Finset.mem_image.mpr ⟨edge, hEdge, ?_⟩
      rw [SheetPartition.mem_block_iff] at hBlock
      unfold SheetPartition.Rel at hBlock
      rw [← hBlock]
      exact (survivor_repr hEdge).symm
    · intro hMem
      obtain ⟨edge, hEdge, rfl⟩ := Finset.mem_image.mp hMem
      refine Finset.mem_image.mpr ⟨occurrenceSheet edge, ?_, survivor_repr hEdge⟩
      exact Finset.mem_biUnion.mpr ⟨edge, hEdge,
        (data.edgePartition (star.edge label)).self_mem_block _⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage]
  exact Finset.card_image_of_injOn fun first hFirst second hSecond hEq ↦
    eq_of_occurrenceSheet_eq (Finset.mem_coe.mp hFirst) (Finset.mem_coe.mp hSecond) hEq

/-! ## 3.  The thick direction and the two selected survivors -/

namespace Prescribed

private theorem succ_ne_self (label : Fin 2) : label + 1 ≠ label := by
  revert label; decide

/-- The target occurrence carrying at least two survivors: in Configuration A
either one of the two, in Configuration B the tripled one.  The subdivision
point `u` of the outgoing base tree is placed on it. -/
noncomputable def thickDirection (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) : Fin 2 :=
  if 2 ≤ (directionSurvivors data star anchor 0).card then 0 else 1

/-- The other target occurrence, carried by the endpoint `v`. -/
noncomputable def thinDirection (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) : Fin 2 :=
  thickDirection data star anchor + 1

theorem thinDirection_ne (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    thinDirection data star anchor ≠ thickDirection data star anchor :=
  succ_ne_self _

/-- The literal thick target occurrence, the paper's `t_2`. -/
noncomputable def thickEdge (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) : target.edges :=
  star.edge (thickDirection data star anchor)

/-- The literal thin target occurrence, the paper's `t_3`. -/
noncomputable def thinEdge (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) : target.edges :=
  star.edge (thinDirection data star anchor)

theorem thinEdge_ne_thickEdge (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    thinEdge data star anchor ≠ thickEdge data star anchor := by
  intro hEq
  exact thinDirection_ne data star anchor (star.edge_injective hEq)

theorem thickEdge_mem_incidentEdges (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    thickEdge data star anchor ∈ GluingDatum.incidentEdges wall :=
  star.edge_mem_incidentEdges _

theorem thinEdge_mem_incidentEdges (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    thinEdge data star anchor ∈ GluingDatum.incidentEdges wall :=
  star.edge_mem_incidentEdges _

/-- **Both distributions supply the thick direction.**  In the `2 + 2` split
both directions carry two survivors; in the `3 + 1` split the tripled one
carries three. -/
theorem two_le_card_thick (source : TwoBranchAnchor data star anchor) :
    2 ≤ (directionSurvivors data star anchor (thickDirection data star anchor)).card := by
  classical
  unfold thickDirection
  by_cases hZero : 2 ≤ (directionSurvivors data star anchor 0).card
  · rw [if_pos hZero]; exact hZero
  · rw [if_neg hZero]
    rcases source.distribution with hEven | ⟨tripled, hTripled, hOther⟩
    · exact absurd (le_of_eq (hEven 0).symm) hZero
    · have hTripledNe : tripled ≠ 0 := by
        intro hEq
        rw [hEq] at hTripled
        omega
      rcases NonTrivalentValencyTwoAnchor.eq_zero_or_one tripled with hZeroCase | hOneCase
      · exact absurd hZeroCase hTripledNe
      · rw [← hOneCase, hTripled]
        omega

theorem exists_selected_pair (source : TwoBranchAnchor data star anchor) :
    ∃ first second, first ≠ second ∧
      first ∈ directionSurvivors data star anchor (thickDirection data star anchor) ∧
      second ∈ directionSurvivors data star anchor (thickDirection data star anchor) := by
  obtain ⟨first, hFirst, second, hSecond, hNe⟩ :=
    Finset.one_lt_card.mp (two_le_card_thick source)
  exact ⟨first, second, hNe, hFirst, hSecond⟩

/-- **The prescribed pair.**  In Configuration B (`3 + 1`) Part II
prescribes *which* two of the three survivors above the thick occurrence are
merged: the three merge members of Base II are exactly the three choices, and a
prescribed Whitehead move on the stable source realises one of them.  The pair
is therefore data, not a `Classical.choose`, exactly as the pairing
`Fin 3` is data in the valency-four candidate; `Selection.default` recovers the
choice-made instance and `Selection.nonempty` is the non-vacuity witness. -/
structure Selection (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) where
  /-- the first selected survivor above the thick target occurrence -/
  first : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)
  /-- the second selected survivor above the thick target occurrence -/
  second : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)
  /-- the two selected occurrences are distinct -/
  first_ne_second : first ≠ second
  /-- the first one lies above the thick target occurrence -/
  first_mem : first ∈ directionSurvivors data star anchor (thickDirection data star anchor)
  /-- the second one lies above the thick target occurrence -/
  second_mem : second ∈ directionSurvivors data star anchor (thickDirection data star anchor)

namespace Selection

/-- The distinguished selection made by `exists_selected_pair`, a default
instance of the prescribed pair. -/
noncomputable def default (source : TwoBranchAnchor data star anchor) :
    Selection data star anchor where
  first := Classical.choose (exists_selected_pair source)
  second := Classical.choose (Classical.choose_spec (exists_selected_pair source))
  first_ne_second :=
    (Classical.choose_spec (Classical.choose_spec (exists_selected_pair source))).1
  first_mem :=
    (Classical.choose_spec (Classical.choose_spec (exists_selected_pair source))).2.1
  second_mem :=
    (Classical.choose_spec (Classical.choose_spec (exists_selected_pair source))).2.2

/-- **Non-vacuity of `Selection`.**  Above a two-branch anchor a prescribed pair
always exists: both distributions leave a direction with at least two
survivors. -/
theorem nonempty (source : TwoBranchAnchor data star anchor) :
    Nonempty (Selection data star anchor) :=
  ⟨default source⟩

end Selection

variable (source : TwoBranchAnchor data star anchor)
  (sel : Selection data star anchor)

/-- The paper's selected occurrence `e_first` above the thick direction. -/
def firstSelected :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  sel.first

/-- The paper's selected occurrence `e_second` above the thick direction. -/
def secondSelected :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor) :=
  sel.second

theorem firstSelected_ne_secondSelected :
    firstSelected sel ≠ secondSelected sel :=
  sel.first_ne_second

theorem firstSelected_mem :
    firstSelected sel ∈
      directionSurvivors data star anchor (thickDirection data star anchor) :=
  sel.first_mem

theorem secondSelected_mem :
    secondSelected sel ∈
      directionSurvivors data star anchor (thickDirection data star anchor) :=
  sel.second_mem

/-- The two selected classes are distinct blocks of one and the same edge
partition, so the merge below needs no branch gauge. -/
theorem not_rel_selected :
    ¬(data.edgePartition (thickEdge data star anchor)).Rel
      (occurrenceSheet (firstSelected sel))
      (occurrenceSheet (secondSelected sel)) :=
  not_rel_occurrenceSheet (firstSelected_mem sel) (secondSelected_mem sel)
    (firstSelected_ne_secondSelected sel)

/-- The canonical sheet naming the new bridge class. -/
noncomputable def selectedRepresentative : Fin degree :=
  occurrenceSheet (firstSelected sel)

theorem selectedRepresentative_wall_rel :
    (data.vertexPartition wall).Rel anchor.1 (selectedRepresentative sel) :=
  occurrenceSheet_wall_rel _

/-- The literal `A_u`-class of the paper: the honest union of the two selected
surviving classes. -/
noncomputable def selectedSheets : Finset (Fin degree) :=
  (data.edgePartition (thickEdge data star anchor)).block
      (occurrenceSheet (firstSelected sel)) ∪
    (data.edgePartition (thickEdge data star anchor)).block
      (occurrenceSheet (secondSelected sel))

/-- The exact size of the new bridge class: `k_first + k_second`, with no
`-1`, because the two classes are disjoint. -/
theorem selectedSheets_card :
    (selectedSheets sel).card =
      data.sourceEdgeIndex (firstSelected sel).1 +
        data.sourceEdgeIndex (secondSelected sel).1 := by
  classical
  have hDisjoint :
      (data.edgePartition (thickEdge data star anchor)).block
          (occurrenceSheet (firstSelected sel)) ∩
        (data.edgePartition (thickEdge data star anchor)).block
          (occurrenceSheet (secondSelected sel)) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem ?_
    intro sheet hSheet
    rw [Finset.mem_inter, SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
      at hSheet
    exact not_rel_selected sel (hSheet.1.trans hSheet.2.symm)
  have hUnion := Finset.card_union_add_card_inter
    ((data.edgePartition (thickEdge data star anchor)).block
      (occurrenceSheet (firstSelected sel)))
    ((data.edgePartition (thickEdge data star anchor)).block
      (occurrenceSheet (secondSelected sel)))
  rw [hDisjoint] at hUnion
  simp only [Finset.card_empty, Nat.add_zero] at hUnion
  rw [sourceEdgeIndex_eq_blockCard (firstSelected_mem sel),
    sourceEdgeIndex_eq_blockCard (secondSelected_mem sel)]
  exact hUnion

/-- The endpoint partition over the divalent subdivision point `u`: the thick
direction's own classes, with the two selected ones joined. -/
noncomputable def finePartition : SheetPartition degree :=
  (data.edgePartition (thickEdge data star anchor)).mergeBlocks
    (occurrenceSheet (firstSelected sel))
    (occurrenceSheet (secondSelected sel)) (not_rel_selected sel)

theorem finePartition_block_selected :
    (finePartition sel).block (selectedRepresentative sel) =
      selectedSheets sel :=
  SheetPartition.mergeBlocks_block_first _ _ _ _

/-- The exact new-edge size on the local resolution. -/
theorem finePartition_blockCard_selected :
    (finePartition sel).blockCard (selectedRepresentative sel) =
      data.sourceEdgeIndex (firstSelected sel).1 +
        data.sourceEdgeIndex (secondSelected sel).1 := by
  unfold SheetPartition.blockCard
  rw [finePartition_block_selected sel]
  exact selectedSheets_card sel

theorem edgePartition_thick_refines_finePartition :
    (data.edgePartition (thickEdge data star anchor)).Refines (finePartition sel) :=
  refines_mergeBlocks _ _ _ _

theorem finePartition_refines :
    (finePartition sel).Refines (data.vertexPartition wall) :=
  mergeBlocks_refines _ _ _ _ _
    (star.edgePartition_refines_wall data (thickDirection data star anchor))
    ((occurrenceSheet_wall_rel (firstSelected sel)).symm.trans
      (occurrenceSheet_wall_rel (secondSelected sel)))

/-! ## 4.  The outgoing base tree: the divalent wall is subdivided -/

/-- The occurrence assignment of the outgoing base tree: the thick direction
stays at the divalent endpoint `u`, the thin direction moves to the divalent
endpoint `v`.  This is Part I's `T_2` (Case {w2}), Part II's Base II. -/
noncomputable def rightAssignment (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    target.edges → Bool :=
  fun edge ↦ decide (edge ≠ thickEdge data star anchor)

@[simp] theorem rightAssignment_thick (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    rightAssignment data star anchor (thickEdge data star anchor) = false := by
  simp [rightAssignment]

theorem rightAssignment_of_ne (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    {edge : target.edges} (hEdge : edge ≠ thickEdge data star anchor) :
    rightAssignment data star anchor edge = true := by
  simp [rightAssignment, hEdge]

theorem rightAssignment_eq_false_iff (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall)
    (edge : target.edges) :
    rightAssignment data star anchor edge = false ↔ edge = thickEdge data star anchor := by
  simp [rightAssignment]

/-- The single old occurrence at the divalent endpoint `u`. -/
noncomputable def leftEdges (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    List target.edges := [thickEdge data star anchor]

/-- The single old occurrence at the divalent endpoint `v`. -/
noncomputable def rightEdges (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    List target.edges := [thinEdge data star anchor]

theorem incidentEdges_eq_pair (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    GluingDatum.incidentEdges wall =
      {thickEdge data star anchor, thinEdge data star anchor} := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl
    · exact thickEdge_mem_incidentEdges data star anchor
    · exact thinEdge_mem_incidentEdges data star anchor
  · rw [star.card_incidentEdges,
      Finset.card_insert_of_notMem (by
        simp [Ne.symm (thinEdge_ne_thickEdge data star anchor)]),
      Finset.card_singleton]

theorem wallEdgesAssigned_false (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    wallEdgesAssigned target wall (rightAssignment data star anchor) false =
      {thickEdge data star anchor} := by
  classical
  ext edge
  rw [mem_wallEdgesAssigned, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hSide⟩
    exact (rightAssignment_eq_false_iff data star anchor edge).mp hSide
  · rintro rfl
    refine ⟨?_, rightAssignment_thick data star anchor⟩
    exact (GluingContraction.mem_incidentEdges_iff wall _).mp
      (thickEdge_mem_incidentEdges data star anchor)

theorem wallEdgesAssigned_true (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    wallEdgesAssigned target wall (rightAssignment data star anchor) true =
      {thinEdge data star anchor} := by
  classical
  ext edge
  rw [mem_wallEdgesAssigned, Finset.mem_singleton]
  constructor
  · rintro ⟨hIncident, hSide⟩
    have hMem : edge ∈ GluingDatum.incidentEdges wall :=
      (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
    rw [incidentEdges_eq_pair data star anchor] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with rfl | hThin
    · rw [rightAssignment_thick data star anchor] at hSide
      exact absurd hSide (by simp)
    · exact hThin
  · rintro rfl
    exact ⟨(GluingContraction.mem_incidentEdges_iff wall _).mp
        (thinEdge_mem_incidentEdges data star anchor),
      rightAssignment_of_ne data star anchor (thinEdge_ne_thickEdge data star anchor)⟩

theorem leftEdges_eq (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    ((leftEdges data star anchor : List target.edges) : Multiset target.edges) =
      (wallEdgesAssigned target wall (rightAssignment data star anchor) false).val := by
  rw [wallEdgesAssigned_false data star anchor]
  rfl

theorem rightEdges_eq (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    ((rightEdges data star anchor : List target.edges) : Multiset target.edges) =
      (wallEdgesAssigned target wall (rightAssignment data star anchor) true).val := by
  rw [wallEdgesAssigned_true data star anchor]
  rfl

/-! ## 5.  The local resolution at the anchor and both endpoint inequalities -/

/-- The prescribed local resolution of case `{v2-nd4}`: the divalent side `u`
carries the merged thick partition and the divalent side `v` keeps the whole
old wall block, so `|A_v| = |A|`. -/
noncomputable def selectedResolution : LocalResolution degree :=
  fineResolution (data.vertexPartition wall) (finePartition sel)
    (finePartition_refines sel)

@[simp] theorem selectedResolution_left :
    (selectedResolution sel).left = finePartition sel := rfl

@[simp] theorem selectedResolution_right :
    (selectedResolution sel).right = data.vertexPartition wall := rfl

@[simp] theorem selectedResolution_newEdge :
    (selectedResolution sel).newEdge = finePartition sel := rfl

theorem selectedResolution_contracts :
    (selectedResolution sel).ContractsTo (data.vertexPartition wall) :=
  fineResolution_contracts _ _ _

/-- Exterior compatibility with both old occurrences at the wall. -/
theorem selected_exterior (edge : target.edges)
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    (data.edgePartition edge).Refines
      (if rightAssignment data star anchor edge then (selectedResolution sel).right
        else (selectedResolution sel).left) := by
  classical
  have hMem : edge ∈ GluingDatum.incidentEdges wall :=
    (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
  by_cases hEdge : edge = thickEdge data star anchor
  · subst hEdge
    rw [rightAssignment_thick data star anchor, if_neg (by simp)]
    exact edgePartition_thick_refines_finePartition sel
  · rw [rightAssignment_of_ne data star anchor hEdge, if_pos rfl]
    exact edgePartition_refines_of_mem_incidentEdges data wall edge hMem

/-- The endpoint `u` is divalent, so its Riemann--Hurwitz inequality is
automatic. -/
theorem selected_riemannHurwitz_left (block : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (selectedResolution sel).left
      ((selectedResolution sel).newEdge ::
        (leftEdges data star anchor).map data.edgePartition) block := by
  simpa [leftEdges] using riemannHurwitzAtBlock_divalent (data.vertexPartition wall)
    (selectedResolution sel).left (selectedResolution sel).newEdge
    (data.edgePartition (thickEdge data star anchor)) block

/-- The endpoint `v` is divalent as well: this is the whole gain of the Base II
base tree over Base I, whose trivalent endpoint would need an index
condition. -/
theorem selected_riemannHurwitz_right (block : Fin degree) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (selectedResolution sel).right
      ((selectedResolution sel).newEdge ::
        (rightEdges data star anchor).map data.edgePartition) block := by
  simpa [rightEdges] using riemannHurwitzAtBlock_divalent (data.vertexPartition wall)
    (selectedResolution sel).right (selectedResolution sel).newEdge
    (data.edgePartition (thinEdge data star anchor)) block

/-! ## 6.  The exact counts behind the two inequalities

At a divalent target endpoint Part II's change-minimality reads `ch = 1`.  The
two theorems of this section are the block-count form of that statement for the
anchor: the new vertex over `u` through the selected representative and the new
vertex `A_v = A` over `v` are both *trivalent*, so each carries local
ramification exactly `3 - 2 = 1`.  Both use the valency-two index identities
through `blockCountWithin_eq_card_directionSurvivors`. -/

theorem thickEdge_eq (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    thickEdge data star anchor = star.edge (thickDirection data star anchor) := rfl

theorem thinEdge_eq (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    thinEdge data star anchor = star.edge (thinDirection data star anchor) := rfl

private theorem block_image_repr {d : ℕ} (partition : SheetPartition d) (x : Fin d) :
    (partition.block x).image partition.repr = {partition.repr x} := by
  classical
  ext representative
  simp only [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨sheet, hSheet, rfl⟩
    rw [SheetPartition.mem_block_iff] at hSheet
    exact hSheet.symm
  · rintro rfl
    exact ⟨x, partition.self_mem_block x, rfl⟩

theorem finePartition_block_first :
    (finePartition sel).block (occurrenceSheet (firstSelected sel)) =
      selectedSheets sel :=
  SheetPartition.mergeBlocks_block_first _ _ _ _

theorem occurrenceSheet_mem_wallBlock
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)) :
    occurrenceSheet edge ∈ (data.vertexPartition wall).block anchor.1 :=
  ((data.vertexPartition wall).mem_block_iff _ _).mpr (occurrenceSheet_wall_rel edge)

/-- **The `u`-side census.**  The selected bridge class sees exactly the two
selected old occurrences, so the new vertex over `u` is trivalent. -/
theorem left_endpoint_thick_blockCount :
    (data.edgePartition (thickEdge data star anchor)).blockCountWithin
        (finePartition sel) (selectedRepresentative sel) = 2 := by
  classical
  have hBlock : (finePartition sel).block (selectedRepresentative sel) =
      selectedSheets sel := finePartition_block_first sel
  have hImage :
      ((finePartition sel).block (selectedRepresentative sel)).image
          (data.edgePartition (thickEdge data star anchor)).repr =
        insert ((data.edgePartition (thickEdge data star anchor)).repr
            (occurrenceSheet (firstSelected sel)))
          {(data.edgePartition (thickEdge data star anchor)).repr
            (occurrenceSheet (secondSelected sel))} := by
    rw [hBlock]
    unfold selectedSheets
    rw [Finset.image_union, block_image_repr, block_image_repr, Finset.singleton_union]
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact fun hEq ↦ not_rel_selected sel hEq), Finset.card_singleton]

include source in
/-- Every direction fibre of the `2 + 2` and `3 + 1` splits has the other one
as its complement in four survivors. -/
theorem card_thick_add_card_thin :
    (directionSurvivors data star anchor (thickDirection data star anchor)).card +
      (directionSurvivors data star anchor (thinDirection data star anchor)).card = 4 := by
  have hGeneral : ∀ label : Fin 2,
      (directionSurvivors data star anchor label).card +
        (directionSurvivors data star anchor (label + 1)).card = 4 := by
    intro label
    rcases source.distribution with hEven | ⟨tripled, hTripled, hOther⟩
    · rw [hEven, hEven]
    · rcases NonTrivalentValencyTwoAnchor.eq_zero_or_one label with hLabel | hLabel <;>
        rcases NonTrivalentValencyTwoAnchor.eq_zero_or_one tripled with hTrip | hTrip <;>
        subst hLabel <;> subst hTrip
      · rw [show ((0 : Fin 2) + 1) = 1 from rfl, hTripled, hOther 1 (by decide)]
      · rw [show ((0 : Fin 2) + 1) = 1 from rfl, hTripled, hOther 0 (by decide)]
      · rw [show ((1 : Fin 2) + 1) = 0 from rfl, hTripled, hOther 1 (by decide)]
      · rw [show ((1 : Fin 2) + 1) = 0 from rfl, hTripled, hOther 0 (by decide)]
  exact hGeneral (thickDirection data star anchor)

include source in
/-- The number of bridge occurrences inside `A`: one fewer than the thick
direction's survivors, because exactly two of them were merged. -/
theorem finePartition_blockCountWithin :
    (finePartition sel).blockCountWithin (data.vertexPartition wall) anchor.1 =
      (directionSurvivors data star anchor (thickDirection data star anchor)).card - 1 := by
  classical
  have hSecondMem := secondSelected_mem sel
  have hFirstMem := firstSelected_mem sel
  have hFirstRetained : firstSelected sel ∈
      (directionSurvivors data star anchor (thickDirection data star anchor)).erase
        (secondSelected sel) :=
    Finset.mem_erase.mpr ⟨firstSelected_ne_secondSelected sel, hFirstMem⟩
  have hSelectedRel : (finePartition sel).Rel
      (occurrenceSheet (firstSelected sel))
      (occurrenceSheet (secondSelected sel)) := by
    have hMem : occurrenceSheet (secondSelected sel) ∈
        (finePartition sel).block (occurrenceSheet (firstSelected sel)) := by
      rw [finePartition_block_first sel]
      exact Finset.mem_union_right _
        ((data.edgePartition (thickEdge data star anchor)).self_mem_block _)
    exact (SheetPartition.mem_block_iff _ _ _).mp hMem
  have hMergedMem : ∀ edge ∈ directionSurvivors data star anchor
        (thickDirection data star anchor),
      (finePartition sel).Rel (occurrenceSheet (firstSelected sel))
          (occurrenceSheet edge) →
        edge = firstSelected sel ∨ edge = secondSelected sel := by
    intro edge hEdge hRel
    have hMem : occurrenceSheet edge ∈
        (finePartition sel).block (occurrenceSheet (firstSelected sel)) :=
      (SheetPartition.mem_block_iff _ _ _).mpr hRel
    rw [finePartition_block_first sel] at hMem
    unfold selectedSheets at hMem
    rcases Finset.mem_union.mp hMem with hCase | hCase
    · left
      rw [SheetPartition.mem_block_iff] at hCase
      by_contra hNe
      rw [thickEdge_eq] at hCase
      exact not_rel_occurrenceSheet hFirstMem hEdge (fun h ↦ hNe h.symm) hCase
    · right
      rw [SheetPartition.mem_block_iff] at hCase
      by_contra hNe
      rw [thickEdge_eq] at hCase
      exact not_rel_occurrenceSheet hSecondMem hEdge (fun h ↦ hNe h.symm) hCase
  have hOtherBlock : ∀ edge ∈ directionSurvivors data star anchor
        (thickDirection data star anchor),
      edge ≠ firstSelected sel → edge ≠ secondSelected sel →
      (finePartition sel).block (occurrenceSheet edge) =
        (data.edgePartition (thickEdge data star anchor)).block (occurrenceSheet edge) := by
    intro edge hEdge hNeFirst hNeSecond
    exact SheetPartition.mergeBlocks_block_of_separate _ _ _ _ _
      (not_rel_occurrenceSheet hEdge hFirstMem hNeFirst)
      (not_rel_occurrenceSheet hEdge hSecondMem hNeSecond)
  have hInj : ∀ edgeA ∈ (directionSurvivors data star anchor
        (thickDirection data star anchor)).erase (secondSelected sel),
      ∀ edgeB ∈ (directionSurvivors data star anchor
        (thickDirection data star anchor)).erase (secondSelected sel),
      (finePartition sel).repr (occurrenceSheet edgeA) =
        (finePartition sel).repr (occurrenceSheet edgeB) → edgeA = edgeB := by
    intro edgeA hA edgeB hB hEq
    obtain ⟨hANe, hAMem⟩ := Finset.mem_erase.mp hA
    obtain ⟨hBNe, hBMem⟩ := Finset.mem_erase.mp hB
    have hRel : (finePartition sel).Rel (occurrenceSheet edgeA)
        (occurrenceSheet edgeB) := hEq
    by_cases hAFirst : edgeA = firstSelected sel
    · subst hAFirst
      rcases hMergedMem edgeB hBMem hRel with hCase | hCase
      · exact hCase.symm
      · exact absurd hCase hBNe
    · have hBlock := hOtherBlock edgeA hAMem hAFirst hANe
      have hMem : occurrenceSheet edgeB ∈
          (finePartition sel).block (occurrenceSheet edgeA) :=
        (SheetPartition.mem_block_iff _ _ _).mpr hRel
      rw [hBlock, SheetPartition.mem_block_iff, thickEdge_eq] at hMem
      by_contra hNe
      exact not_rel_occurrenceSheet hAMem hBMem hNe hMem
  have hImage :
      ((data.vertexPartition wall).block anchor.1).image (finePartition sel).repr =
        ((directionSurvivors data star anchor
            (thickDirection data star anchor)).erase (secondSelected sel)).image
          (fun edge ↦ (finePartition sel).repr (occurrenceSheet edge)) := by
    ext representative
    constructor
    · intro hMem
      obtain ⟨sheet, hSheet, rfl⟩ := Finset.mem_image.mp hMem
      rw [← biUnion_block_eq_wallBlock source (thickDirection data star anchor)] at hSheet
      obtain ⟨edge, hEdge, hBlock⟩ := Finset.mem_biUnion.mp hSheet
      rw [SheetPartition.mem_block_iff] at hBlock
      have hFine : (finePartition sel).Rel (occurrenceSheet edge) sheet :=
        (edgePartition_thick_refines_finePartition sel).rel hBlock
      by_cases hEdgeSecond : edge = secondSelected sel
      · refine Finset.mem_image.mpr ⟨firstSelected sel, hFirstRetained, ?_⟩
        subst hEdgeSecond
        exact hSelectedRel.trans hFine
      · exact Finset.mem_image.mpr
          ⟨edge, Finset.mem_erase.mpr ⟨hEdgeSecond, hEdge⟩, hFine⟩
    · intro hMem
      obtain ⟨edge, hEdge, rfl⟩ := Finset.mem_image.mp hMem
      exact Finset.mem_image.mpr ⟨occurrenceSheet edge,
        occurrenceSheet_mem_wallBlock edge, rfl⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_image_of_injOn (fun a ha b hb h ↦
      hInj a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) h),
    Finset.card_erase_of_mem hSecondMem]

include source in
/-- **The `v`-side census.**  The new vertex over `v` is the whole old block
`A` and is trivalent: the bridge occurrences plus the thin direction's
survivors number `3`, so its local ramification is `3 - 2 = 1`. -/
theorem right_endpoint_blockCount :
    (finePartition sel).blockCountWithin (data.vertexPartition wall) anchor.1 +
      (data.edgePartition (thinEdge data star anchor)).blockCountWithin
        (data.vertexPartition wall) anchor.1 = 3 := by
  have hFine := finePartition_blockCountWithin source sel
  have hThin : (data.edgePartition (thinEdge data star anchor)).blockCountWithin
      (data.vertexPartition wall) anchor.1 =
      (directionSurvivors data star anchor (thinDirection data star anchor)).card :=
    blockCountWithin_eq_card_directionSurvivors source _
  have hSum := card_thick_add_card_thin source
  have hPos := two_le_card_thick source
  rw [hFine, hThin]
  omega

/-! ## 7.  Configuration A: the bridge is a single occurrence of index `|A|` -/

theorem selectedSheets_subset_wallBlock :
    selectedSheets sel ⊆ (data.vertexPartition wall).block anchor.1 := by
  unfold selectedSheets
  refine Finset.union_subset ?_ ?_
  · rw [thickEdge_eq]
    exact block_subset_wallBlock _ _
  · rw [thickEdge_eq]
    exact block_subset_wallBlock _ _

/-- The bridge never exceeds the local degree. -/
theorem selectedSheets_card_le_blockCard :
    data.sourceEdgeIndex (firstSelected sel).1 +
        data.sourceEdgeIndex (secondSelected sel).1 ≤
      (data.vertexPartition wall).blockCard anchor.1 := by
  rw [← selectedSheets_card sel]
  exact Finset.card_le_card (selectedSheets_subset_wallBlock sel)

include source in
/-- **Configuration A (`{v2-nd4-t3}`).**  When the thick direction carries
exactly two survivors their indices already sum to `|A|`, so the merged class
is all of `A` and the bridge is a single occurrence of index `|A|`. -/
theorem selectedSheets_card_eq_blockCard_of_two
    (hTwo : (directionSurvivors data star anchor
      (thickDirection data star anchor)).card = 2) :
    data.sourceEdgeIndex (firstSelected sel).1 +
        data.sourceEdgeIndex (secondSelected sel).1 =
      (data.vertexPartition wall).blockCard anchor.1 := by
  classical
  have hPair : directionSurvivors data star anchor (thickDirection data star anchor) =
      {firstSelected sel, secondSelected sel} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro edge hEdge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with rfl | rfl
      · exact firstSelected_mem sel
      · exact secondSelected_mem sel
    · rw [hTwo, Finset.card_insert_of_notMem (by
          simp [firstSelected_ne_secondSelected sel]), Finset.card_singleton]
  have hSum := source.direction_index_sum (thickDirection data star anchor)
  rw [hPair, Finset.sum_pair (firstSelected_ne_secondSelected sel)] at hSum
  exact_mod_cast hSum

/-! ## 8.  The guarded background and the installed candidate -/

/-- The source geometry still required away from the distinguished anchor
class: exactly the guarded background resolutions of the other wall blocks. -/
structure SubdivisionBackground (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) where
  resolution : Fin degree → LocalResolution degree
  contracts : ∀ block, ¬(data.vertexPartition wall).Rel anchor.1 block →
    (resolution block).ContractsTo (data.vertexPartition wall)
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    ∀ block, ¬(data.vertexPartition wall).Rel anchor.1 block →
      (data.edgePartition edge).Refines
        (if rightAssignment data star anchor edge then (resolution block).right
          else (resolution block).left)
  left_riemannHurwitz : ∀ block,
    (data.vertexPartition wall).repr block = block →
    ¬(data.vertexPartition wall).Rel anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        (resolution block).left
        ((resolution block).newEdge ::
          (leftEdges data star anchor).map data.edgePartition) block
  right_riemannHurwitz : ∀ block,
    (data.vertexPartition wall).repr block = block →
    ¬(data.vertexPartition wall).Rel anchor.1 block →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        (resolution block).right
        ((resolution block).newEdge ::
          (rightEdges data star anchor).map data.edgePartition) block

namespace SubdivisionBackground

/-- Package the guarded receipts with the subdivided base tree. -/
noncomputable def background (geometry : SubdivisionBackground data star anchor) :
    GlobalM11Arbitrary.Background data wall anchor.1 where
  right := rightAssignment data star anchor
  resolution := geometry.resolution
  contracts := geometry.contracts
  exterior := geometry.exterior
  leftEdges := leftEdges data star anchor
  rightEdges := rightEdges data star anchor
  leftEdges_eq := leftEdges_eq data star anchor
  rightEdges_eq := rightEdges_eq data star anchor
  left_riemannHurwitz := geometry.left_riemannHurwitz
  right_riemannHurwitz := geometry.right_riemannHurwitz

end SubdivisionBackground

/-- **The background producer.**  At a subdivided divalent wall the guarded
receipts need *no* input at all: the neutral joined resolution contracts to the
wall, every incident occurrence partition already refines the wall partition,
and both endpoints are divalent, so their Riemann--Hurwitz inequalities are
automatic.  In particular there is no analogue here of
`NonTrivalentValencyFourBackground.OrdinaryBlockProfile`, no census, and no
`nd <= 3` residual off the anchor -- and, unlike at a trivalent wall, not even
`data.Valid` is consumed. -/
noncomputable def subdivisionBackground (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    SubdivisionBackground data star anchor where
  resolution := fun _ ↦ joinedResolutionAt (data.vertexPartition wall)
  contracts := fun _ _ ↦ joinedResolutionAt_contracts _
  exterior := by
    intro edge hIncident block _
    classical
    have hMem : edge ∈ GluingDatum.incidentEdges wall :=
      (GluingContraction.mem_incidentEdges_iff wall edge).mpr hIncident
    by_cases hEdge : edge = thickEdge data star anchor
    · subst hEdge
      rw [rightAssignment_thick data star anchor, if_neg (by simp)]
      exact edgePartition_refines_of_mem_incidentEdges data wall _ hMem
    · rw [rightAssignment_of_ne data star anchor hEdge, if_pos rfl]
      exact edgePartition_refines_of_mem_incidentEdges data wall edge hMem
  left_riemannHurwitz := by
    intro block _ _
    exact riemannHurwitzAtBlock_divalent _ _ _ _ _
  right_riemannHurwitz := by
    intro block _ _
    exact riemannHurwitzAtBlock_divalent _ _ _ _ _

/-- Non-vacuity of the guarded background: it is inhabited for every gluing
datum whatsoever.  (There is no degree-one witness: a `TwoBranchAnchor` forces
`2|A| = k_2 + k_3 + k_4 + k_5 >= 4`, hence `|A| >= 2`.) -/
theorem nonempty_subdivisionBackground (data : GluingDatum target degree)
    (star : TwoStar target wall) (anchor : WallBlock data wall) :
    Nonempty (SubdivisionBackground data star anchor) :=
  ⟨subdivisionBackground data star anchor⟩

/-- The prescribed valency-two resolution installed into the guarded
background: an actual globally assembled candidate over the *unchanged*
incoming datum, since no branch gauge is needed. -/
noncomputable def candidate (geometry : SubdivisionBackground data star anchor) :
    BalancedGlobal.Candidate target degree data wall := by
  apply (SubdivisionBackground.background geometry).install
    (selectedResolution sel) (selectedResolution_contracts sel)
    (selected_exterior sel)
  · intro block _ _
    exact selected_riemannHurwitz_left sel block
  · intro block _ _
    exact selected_riemannHurwitz_right sel block

theorem candidate_datum_valid (geometry : SubdivisionBackground data star anchor)
    (hValid : data.Valid) : (candidate sel geometry).datum.Valid :=
  (candidate sel geometry).datum_valid hValid

theorem candidate_resolution_of_wall_rel
    (geometry : SubdivisionBackground data star anchor) (block : Fin degree)
    (hRel : (data.vertexPartition wall).Rel anchor.1 block) :
    (candidate sel geometry).resolution block = selectedResolution sel := by
  unfold candidate SubdivisionBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_rel _ _ _ _ _ hRel

theorem candidate_resolution_anchor
    (geometry : SubdivisionBackground data star anchor) :
    (candidate sel geometry).resolution anchor.1 = selectedResolution sel :=
  candidate_resolution_of_wall_rel sel geometry anchor.1 rfl

/-- Exact bridge size on the candidate's distinguished local resolution. -/
theorem candidate_newEdge_blockCard
    (geometry : SubdivisionBackground data star anchor) :
    ((candidate sel geometry).resolution anchor.1).newEdge.blockCard
        (selectedRepresentative sel) =
      data.sourceEdgeIndex (firstSelected sel).1 +
        data.sourceEdgeIndex (secondSelected sel).1 := by
  rw [candidate_resolution_anchor sel geometry, selectedResolution_newEdge]
  exact finePartition_blockCard_selected sel

/-- The same bridge size read in the outgoing gluing datum itself. -/
theorem candidate_newSourceEdge_index
    (geometry : SubdivisionBackground data star anchor) :
    (candidate sel geometry).datum.sourceEdgeIndex
        ((candidate sel geometry).newSourceEdge (selectedRepresentative sel)) =
      data.sourceEdgeIndex (firstSelected sel).1 +
        data.sourceEdgeIndex (secondSelected sel).1 := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard]
  have hRepr : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr (selectedRepresentative sel)) :=
    (selectedRepresentative_wall_rel sel).trans
      ((data.vertexPartition wall).rel_repr_right _)
  rw [candidate_resolution_of_wall_rel sel geometry _ hRepr,
    selectedResolution_newEdge]
  exact finePartition_blockCard_selected sel

private theorem blockCard_congr' {d : ℕ} (partition : SheetPartition d)
    {first second : Fin d} (hRel : partition.Rel first second) :
    partition.blockCard first = partition.blockCard second := by
  unfold SheetPartition.blockCard
  rw [partition.block_eq_of_rel hRel]

/-- The exact endpoint sizes: the merged class on the `u` side and the whole
old block `|A_v| = |A|` on the `v` side. -/
theorem candidate_endpoint_blockCard
    (geometry : SubdivisionBackground data star anchor) (sideValue : Bool) :
    (if sideValue then ((candidate sel geometry).resolution anchor.1).right
      else ((candidate sel geometry).resolution anchor.1).left).blockCard
        (selectedRepresentative sel) =
      if sideValue then (data.vertexPartition wall).blockCard anchor.1
      else data.sourceEdgeIndex (firstSelected sel).1 +
        data.sourceEdgeIndex (secondSelected sel).1 := by
  rw [candidate_resolution_anchor sel geometry]
  cases sideValue
  · simpa using finePartition_blockCard_selected sel
  · simp only [selectedResolution_right]
    exact blockCard_congr' _ (selectedRepresentative_wall_rel sel).symm

/-! ## 9.  The candidate with no background hypothesis -/

/-- The valency-two candidate itself, with **no** background hypothesis and no
`DanglingEdgeNoGlue` hypothesis. -/
noncomputable def validCandidate : BalancedGlobal.Candidate target degree data wall :=
  candidate sel (subdivisionBackground data star anchor)

theorem validCandidate_datum_valid (hValid : data.Valid) :
    (validCandidate sel).datum.Valid :=
  candidate_datum_valid sel _ hValid

theorem validCandidate_newEdge_blockCard :
    ((validCandidate sel).resolution anchor.1).newEdge.blockCard
        (selectedRepresentative sel) =
      data.sourceEdgeIndex (firstSelected sel).1 +
        data.sourceEdgeIndex (secondSelected sel).1 :=
  candidate_newEdge_blockCard sel _

theorem validCandidate_endpoint_blockCard (sideValue : Bool) :
    (if sideValue then ((validCandidate sel).resolution anchor.1).right
      else ((validCandidate sel).resolution anchor.1).left).blockCard
        (selectedRepresentative sel) =
      if sideValue then (data.vertexPartition wall).blockCard anchor.1
      else data.sourceEdgeIndex (firstSelected sel).1 +
        data.sourceEdgeIndex (secondSelected sel).1 :=
  candidate_endpoint_blockCard sel _ sideValue

end Prescribed

/-! ## 10.  The incoming-cover form

The shape of `NonTrivalentValencyThreeCandidate.exists_valid_candidate_of_contraction`
at valency two.  Everything except `hNd` is supplied by the incoming
full-dimensional cover and its contraction forest; `hNd` (the anchor's
surviving valency is four) stays an explicit hypothesis, exactly as at
valency three. -/

section Incoming

open GraphContraction GluingContraction ContractionFibre ContractionRamification
open FullDimensionalSource WallDegeneration

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- From an actual incoming full-dimensional cover, its contraction forest and
an anchor of surviving valency four above a divalent wall: the prescribed
valency-two candidate exists, its outgoing datum is valid, and its bridge and
endpoint sizes are the exact source values `k_first + k_second` and `|A|`.  No
background, census, no-glue or ramification receipt is supplied. -/
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
        anchorBlock) = 4) :
    ∃ _source : NonTrivalentValencyTwoAnchor.TwoBranchAnchor
        (contractDatum data hc hab hOne) star anchorBlock,
      ∀ sel : Prescribed.Selection (contractDatum data hc hab hOne) star anchorBlock,
      (Prescribed.validCandidate sel).datum.Valid ∧
      ((Prescribed.validCandidate sel).resolution anchorBlock.1).newEdge.blockCard
          (Prescribed.selectedRepresentative sel) =
        (contractDatum data hc hab hOne).sourceEdgeIndex
            (Prescribed.firstSelected sel).1 +
          (contractDatum data hc hab hOne).sourceEdgeIndex
            (Prescribed.secondSelected sel).1 ∧
      (∀ sideValue : Bool,
        (if sideValue then
            ((Prescribed.validCandidate sel).resolution anchorBlock.1).right
          else ((Prescribed.validCandidate sel).resolution anchorBlock.1).left).blockCard
              (Prescribed.selectedRepresentative sel) =
          if sideValue then
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
              anchorBlock.1
          else (contractDatum data hc hab hOne).sourceEdgeIndex
              (Prescribed.firstSelected sel).1 +
            (contractDatum data hc hab hOne).sourceEdgeIndex
              (Prescribed.secondSelected sel).1) ∧
      (Prescribed.finePartition sel).blockCountWithin
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) anchorBlock.1 +
          ((contractDatum data hc hab hOne).edgePartition
            (Prescribed.thinEdge (contractDatum data hc hab hOne) star anchorBlock)).blockCountWithin
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) anchorBlock.1 = 3 := by
  set source := NonTrivalentValencyTwoRigidity.twoBranchAnchor data fd hc hab hOne
    hForest hCompat star anchorBlock hNd with hSource
  refine ⟨source, fun sel ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · exact Prescribed.validCandidate_datum_valid sel
      (valid_contractDatum data hc hab hOne hForest fd.valid)
  · exact Prescribed.validCandidate_newEdge_blockCard sel
  · exact Prescribed.validCandidate_endpoint_blockCard sel
  · exact Prescribed.right_endpoint_blockCount source sel

end Incoming

/-! ## 11.  Non-vacuity

`subdivisionBackground` is an unconditional literal inhabitant of the only new
structure introduced here, so `SubdivisionBackground` is not empty.  No
inhabitant of `TwoBranchAnchor` over a literal gluing datum is exhibited, for
the same reason as in `NonTrivalentValencyTwoAnchor` and
`NonTrivalentValencyThreeCandidate`: that would need an explicit
`FullDimensionalSourcePresentation`.  The arithmetic of every configuration is
therefore discharged on literal inputs, so none of the definitions above is
empty by arithmetic accident. -/

section NonVacuity

/-- Configuration A, subcase `{v2-nd4-t3-k2=k4}` (all indices equal):
`|A| = 2`, `k = (1,1,1,1)`.  The thick direction has two survivors, the merged
bridge class is `k_3 + k_4 = 2 = |A|`, and the `v`-side census is
`(2 - 1) + 2 = 3`. -/
theorem configurationA_equal_witness :
    (1 + 1 : ℕ) = 2 ∧ (1 + 1 : ℕ) = 2 ∧ (2 - 1) + 2 = 3 ∧ (1 + 2 : ℕ) = 3 := by
  norm_num

/-- Configuration A, subcase `{v2-nd4-t3-k2<k3}` (strict chain):
`|A| = 6`, `k = (1,2,4,5)` with `k_3 + k_4 = 2 + 4 = 6` above `t_2` and
`k_2 + k_5 = 1 + 5 = 6` above `t_3`.  The merged bridge class is again all of
`A`, with no index-order condition used.  Base I is *impossible* here, since no
two indices on opposite sides agree. -/
theorem configurationA_strict_witness :
    (2 + 4 : ℕ) = 6 ∧ (1 + 5 : ℕ) = 6 ∧ (2 - 1) + 2 = 3 ∧
      (1 : ℕ) ≠ 2 ∧ (1 : ℕ) ≠ 4 ∧ (2 : ℕ) ≠ 5 ∧ (4 : ℕ) ≠ 5 := by
  norm_num

/-- Configuration B, `{v2-nd4-t2}`: `|A| = k_5 = 3` and
`k_2 = k_3 = k_4 = 1` above the thick direction `t_2`.  Merging two of the
three survivors gives a bridge class of size `2` and leaves one class of size
`1`, so the `u`-side census is `1 + 2 = 3` at the merged vertex, `1 + 1 = 2` at
the remaining one, and the `v`-side census is `(3 - 1) + 1 = 3`.  Every count
is trivalent or divalent, as Part II's change-minimality `ch = 1` at a divalent
target vertex demands. -/
theorem configurationB_witness :
    (1 + 1 + 1 : ℕ) = 3 ∧ (1 + 2 : ℕ) = 3 ∧ (1 + 1 : ℕ) = 2 ∧ (3 - 1) + 1 = 3 := by
  norm_num

/-- The arithmetic of the choice made in §3: both distributions leave a
direction with at least two survivors, which is all the construction needs. -/
theorem thick_direction_exists_witness :
    (2 : ℕ) ≤ 2 ∧ (2 : ℕ) ≤ 3 := by
  norm_num

end NonVacuity

end DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
