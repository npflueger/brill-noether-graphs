module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge
public import DraismaVargas.LocalCases.NonTrivalentValencyFourRows
public import DraismaVargas.LocalCases.NonTrivalentUniqueFourValent
public import DraismaVargas.LocalCases.NonTrivalentAnchorValency
public import DraismaVargas.LocalCases.W2M1kSourceCandidates

@[expose] public section

/-!
# Genus and the endpoint census of the valency-two **Base I** candidates

Source: Vargas, Part II (arXiv:2609.09109), Section 5.4, Configuration A of
Case {v2-nd4} (Case {v2-nd4-t3}), read through the dictionary convention of
Section 5.1, together with Draisma--Vargas Part I (arXiv:1909.12924), Case
{w2-r2}, Base I, whose description of the base tree `T_empty` and of the fibre
above the new leaf is the one followed here.

This module treats `NonTrivalentValencyTwoBaseOne.validCandidate`, the Base I
member of Configuration A, which lives over the gauged datum
`NonTrivalentValencyTwoGauge.gaugedData`.  It is the Base I counterpart of
`NonTrivalentValencyTwoRows` (the Base II member `T_2`).

## The outgoing stable picture

The base tree attaches a new leaf edge `t_1` at the wall: its far endpoint `u`
is a leaf and its near endpoint `v` carries both old occurrences, so
`leafAssignment` sends **every** old occurrence to `v`.  Above the anchor `A`:

* above `u` the block keeps one two-sheet fold `F = {A', A''}` and splits into
  singletons (`SheetPartition.pairBlock`);
* above `v` the block splits into the two `t_2`-classes `A_1`, `A_2`
  (`NonTrivalentValencyTwoBaseOne.refineOnBlock`);
* the new edge splits into index-one occurrences (`SheetPartition.splitBlock`).

At an ordinary wall block the background is `fineResolution` with the block
split into singletons above `u` and kept whole above `v`.

Consequently (`newEdge_rel_iff`) the **whole** new-edge partition is discrete,
and the census reads:

| vertex | surviving star | `nd` |
|---|---|---|
| a singleton above `u` (any block) | none: its one new occurrence dangles | `0` |
| the fold `F` | the two bridge occurrences | `2` |
| `A_1` (resp. `A_2`) | its bridge occurrence + its cross pair | `3` |
| `B_v` over an ordinary block `B` | the old survivors of `B` | `nd(B)` |

So the stable edge `h_1` runs `A_1 -> F -> A_2`: the fold is an *interior*
vertex of the bridge row, not a branch vertex, and an ordinary block is neither
split nor joined by a surviving new occurrence.

## What is proved

* `candidate_sourceGenus`: the Base I candidate preserves the source genus,
  with no further hypothesis.  Unlike the Base II resolution this one is **not** a star in
  the sense of `NonTrivalentValencyFourRows.IsStar` -- both of its endpoint
  partitions differ from the wall partition -- so the blockwise Euler identity
  is proved directly (`selectedResolution_euler`): `|A| + 1 = (|A| - 1) + 2`.
* `not_isDangling_of_third`: the three-vertex survival criterion.  The fold's
  own leaf end is divalent, so the usual "both ends survive" test is
  unavailable; the criterion runs through the fold's *other* occurrence.
* `newSourceEdge_survives_iff`: exactly the two fold occurrences over `t_1`
  survive.
* `nonDanglingValency_leafVertex_fold = 2`,
  `nonDanglingValency_branchVertex_anchor = 3` (with the exact star
  `nonDanglingIncident_branchVertex_anchor`),
  `nonDanglingValency_leafVertex_singleton = 0`,
  `nonDanglingValency_branchVertex_ordinary = nd(B)` (with the exact star
  `nonDanglingIncident_branchVertex_ordinary`).

## What is NOT proved here

* The retained-row descent, the row equivalence, the labelling and the
  statement at an actual wall: those are in
  `NonTrivalentValencyTwoBaseOneRowEquiv`, which imports this module.
* `data.Valid` stays an explicit hypothesis of every census statement, and
  `BaseOneSetup` (hence `nd(A) = 4`, Configuration A and the Base I alignment)
  stays an explicit input; downstream, the gauge of `NonTrivalentValencyTwoGauge`
  supplies the alignment and the wall metric supplies `nd(A) = 4`
  (`NonTrivalentAnchorValency`).
* No matrix, minor or pencil.

## Consumers

`NonTrivalentValencyTwoBaseOneRowEquiv`, and through it the boundary dispatcher
for Part II, Case {v2-nd4} (`NonTrivalentValencyTwoDispatcher`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRows

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
open DraismaVargas.LocalCases.W3R1SourceProfile (survivors mem_survivors card_survivors)
open DraismaVargas.LocalCases.NonTrivalentValencyFourRows (IsStar euler_of_isStar
  isStar_fineResolution)
/-! ## 0.  One partition count -/

section Partitions

variable {d : ℕ}

/-- Refining a coarse partition on one block leaves that block's induced count
unchanged. -/
theorem refineOnBlock_blockCountWithin (coarse fine : SheetPartition d)
    (anchor sheet : Fin d) (hRefines : fine.Refines coarse)
    (hSheet : coarse.Rel anchor sheet) :
    (refineOnBlock coarse fine anchor hRefines).blockCountWithin coarse sheet =
      fine.blockCountWithin coarse sheet := by
  classical
  show ((coarse.block sheet).image
    (refineOnBlock coarse fine anchor hRefines).repr).card =
      ((coarse.block sheet).image fine.repr).card
  refine congrArg Finset.card (Finset.image_congr ?_)
  intro other hOther
  have hMem : other ∈ coarse.block sheet := hOther
  rw [SheetPartition.mem_block_iff] at hMem
  exact refineOnBlock_repr_of_rel coarse fine anchor other hRefines
    (hSheet.trans hMem)

/-- `blockCountWithin` only depends on the coarse block. -/
theorem blockCountWithin_congr (fine coarse : SheetPartition d) {a b : Fin d}
    (h : coarse.Rel a b) :
    fine.blockCountWithin coarse a = fine.blockCountWithin coarse b := by
  classical
  show ((coarse.block a).image fine.repr).card = ((coarse.block b).image fine.repr).card
  rw [coarse.block_eq_of_rel h]

/-- Outside the retained pair, `pairBlock` is discrete on the block. -/
theorem pairBlock_rel_iff_of_ne (partition : SheetPartition d)
    (first second sheet other : Fin d) (hne : first ≠ second)
    (hTogether : partition.Rel first second) (hRel : partition.Rel first sheet)
    (hNeFirst : sheet ≠ first) (hNeSecond : sheet ≠ second) :
    (partition.pairBlock first second hne).Rel sheet other ↔ sheet = other := by
  have hRepr : (partition.pairBlock first second hne).repr sheet = sheet :=
    partition.pairBlock_repr_of_rel_of_ne_second first second sheet hne hRel hNeSecond
  rw [SheetPartition.rel_iff, hRepr]
  constructor
  · intro hEq
    by_cases hOtherSecond : other = second
    · rw [hOtherSecond, partition.pairBlock_repr_second first second hne hTogether] at hEq
      exact absurd hEq hNeFirst
    · by_cases hOtherBlock : partition.Rel first other
      · rw [partition.pairBlock_repr_of_rel_of_ne_second first second other hne
          hOtherBlock hOtherSecond] at hEq
        exact hEq
      · exfalso
        apply hOtherBlock
        rw [partition.pairBlock_repr_of_not_rel first second other hne hOtherBlock] at hEq
        exact (hEq ▸ hRel).trans (partition.rel_repr_left other)
  · rintro rfl
    exact hRepr.symm

end Partitions

/-! ## 1.  The candidate's resolution at every wall block -/

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (setup : BaseOneSetup data star anchor)

local notation "cand" => (validCandidate setup)

/-- Off the anchor block the Base I candidate uses the neutral leaf
background: singletons above the new leaf `u`, the whole block above the new
trivalent point `v`. -/
theorem candidate_resolution_of_not_wall_rel (block : Fin degree)
    (hBlock : ¬ (data.vertexPartition wall).Rel anchor.1 block) :
    (cand).resolution block =
      fineResolution (data.vertexPartition wall)
        ((data.vertexPartition wall).splitBlock block)
        ((data.vertexPartition wall).splitBlock_refines block) := by
  unfold validCandidate candidate LeafBackground.background
    GlobalM11Arbitrary.Background.install
  exact LocalResolution.onBlock_of_not_rel _ _ _ _ _ hBlock

theorem candidate_resolution_anchorBlock (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    (cand).resolution block = selectedResolution setup :=
  NonTrivalentValencyTwoBaseOne.candidate_resolution_of_wall_rel setup
    (leafBackground data star anchor) block hBlock

/-! ## 2.  The source genus is preserved -/

/-- The Base I resolution at the anchor satisfies the blockwise Euler
identity: above the new leaf the block loses one class (the fold), above the
new branch point it has two, and the new edge splits into `|A|` occurrences. -/
theorem selectedResolution_euler (block : Fin degree)
    (hBlock : (data.vertexPartition wall).Rel anchor.1 block) :
    (selectedResolution setup).newEdge.blockCountWithin
        (data.vertexPartition wall) block + 1 =
      (selectedResolution setup).left.blockCountWithin
          (data.vertexPartition wall) block +
        (selectedResolution setup).right.blockCountWithin
          (data.vertexPartition wall) block := by
  have hNew : (selectedResolution setup).newEdge.blockCountWithin
      (data.vertexPartition wall) block =
      (data.vertexPartition wall).blockCard block := by
    rw [selectedResolution_newEdge setup]
    exact (data.vertexPartition wall).splitBlock_blockCountWithin_of_rel anchor.1 block hBlock
  have hLeft : (selectedResolution setup).left.blockCountWithin
      (data.vertexPartition wall) block + 1 =
      (data.vertexPartition wall).blockCard block := by
    rw [selectedResolution_left setup]
    exact W2M1kSourceCandidates.pairBlock_blockCountWithin (data.vertexPartition wall)
      setup.foldFirst setup.foldSecond block setup.foldFirst_ne_foldSecond
      (setup.foldFirst_wall.symm.trans setup.foldSecond_wall)
      (setup.foldFirst_wall.symm.trans hBlock)
  have hRight : (selectedResolution setup).right.blockCountWithin
      (data.vertexPartition wall) block = 2 := by
    rw [selectedResolution_right setup,
      refineOnBlock_blockCountWithin (data.vertexPartition wall)
        (data.edgePartition (star.edge 0)) anchor.1 block
        (star.edgePartition_refines_wall data 0) hBlock,
      ← blockCountWithin_congr (data.edgePartition (star.edge 0))
        (data.vertexPartition wall) hBlock]
    exact blockCountWithin_eq_two setup 0
  omega

/-- **The Base I candidate does not change the source genus.**  No further
hypothesis is needed: the background is a `fineResolution` star at every ordinary block,
and the prescribed resolution satisfies the Euler identity by
`selectedResolution_euler`. -/
theorem candidate_sourceGenus :
    genus (cand).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro block _
  by_cases hBlock : (data.vertexPartition wall).Rel anchor.1 block
  · rw [candidate_resolution_anchorBlock setup block hBlock]
    exact selectedResolution_euler setup block hBlock
  · rw [candidate_resolution_of_not_wall_rel setup block hBlock]
    exact euler_of_isStar (isStar_fineResolution _ _ _) block

/-! ## 2b.  A three-vertex survival criterion -/

section Survival

variable {G : CFGraph} {n : ℕ}

/-- **An occurrence whose far end survives and whose near end carries a second
occurrence to a third surviving vertex is not dangling.**  This is what the
divalent fold above the new leaf needs: its own two ends cannot both be tested
against a surviving vertex, but the fold's *other* occurrence reaches one. -/
theorem not_isDangling_of_third (datum : GluingDatum G n)
    (e f : datum.SourceEdge) {p q r : datum.SourceVertex}
    (hE : datum.sourceEnds e = (p, q)) (hF : datum.sourceEnds f = (p, r))
    (hQR : r ≠ q)
    (hQ : nonDanglingValency datum q ≠ 0)
    (hR : nonDanglingValency datum r ≠ 0) :
    ¬ IsDangling datum e := by
  classical
  have hFst : (datum.sourceEnds e).1 = p := congrArg Prod.fst hE
  have hSnd : (datum.sourceEnds e).2 = q := congrArg Prod.snd hE
  intro hDangling
  rcases hDangling with hSide | hSide
  · obtain ⟨cut⟩ := hSide
    have hPmem : p ∈ cut.side := hFst ▸ cut.left_mem
    by_cases hRmem : r ∈ cut.side
    · exact hR (DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side datum cut hRmem)
    · have hCross := cut.cross_num_edges p r hPmem hRmem
      rw [hSnd] at hCross
      have hZero : num_edges datum.sourceGraph p r = 0 := by
        rw [hCross, ite_eq_right (by
          rintro ⟨-, hEq⟩
          exact hQR hEq)]
      have hPos : 0 < num_edges datum.sourceGraph p r := by
        have := W4StableSource.sourceEnds_num_edges_pos datum f
        rw [hF] at this
        exact this
      omega
  · obtain ⟨cut⟩ := hSide
    have hQmem : q ∈ cut.side := hSnd ▸ cut.left_mem
    exact hQ (DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side datum cut hQmem)

end Survival

/-! ## 3.  The endpoint vertices, the new occurrences, and their partitions -/

theorem not_rel_repr {a : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ¬ (data.vertexPartition wall).Rel anchor.1 ((data.vertexPartition wall).repr a) :=
  fun h ↦ hA (h.trans ((data.vertexPartition wall).rel_repr_right a).symm)

/-- The outgoing source vertex above the new leaf `u` at a sheet. -/
noncomputable def leafVertex (sheet : Fin degree) : (cand).datum.SourceVertex :=
  (cand).datum.sourceEndpoint (oldVertex target wall) sheet

/-- The outgoing source vertex above the new trivalent point `v` at a sheet. -/
noncomputable def branchVertex (sheet : Fin degree) : (cand).datum.SourceVertex :=
  (cand).datum.sourceEndpoint (freshVertex target) sheet

/-- The new occurrence over `t_1` carried by a sheet. -/
noncomputable def bridgeEdge (sheet : Fin degree) : (cand).datum.SourceEdge :=
  (cand).newSourceEdge sheet

theorem sourceEnds_bridgeEdge (sheet : Fin degree) :
    (cand).datum.sourceEnds (bridgeEdge setup sheet) =
      (leafVertex setup sheet, branchVertex setup sheet) :=
  GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ sheet

theorem bridgeEdge_incident_leaf (sheet : Fin degree) :
    Incident (cand).datum (bridgeEdge setup sheet) (leafVertex setup sheet) :=
  Or.inl (congrArg Prod.fst (sourceEnds_bridgeEdge setup sheet))

theorem bridgeEdge_incident_branch (sheet : Fin degree) :
    Incident (cand).datum (bridgeEdge setup sheet) (branchVertex setup sheet) :=
  Or.inr (congrArg Prod.snd (sourceEnds_bridgeEdge setup sheet))

/-! ### The three pasted partitions -/

theorem leafPartition_rel_anchor {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition (oldVertex target wall)).Rel a b ↔
      ((data.vertexPartition wall).pairBlock setup.foldFirst setup.foldSecond
        setup.foldFirst_ne_foldSecond).Rel a b := by
  have hReprRel : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr a) :=
    hA.trans ((data.vertexPartition wall).rel_repr_right a)
  have hSelected := candidate_resolution_anchorBlock setup _ hReprRel
  show ((cand).datum.vertexPartition (oldVertex target wall)).Rel a b ↔ _
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_old_wall]
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).left)
    (fun blk ↦ ((cand).contracts blk).left_refines) a b) ?_
  rw [hSelected]
  rfl

theorem branchPartition_rel_anchor {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition (freshVertex target)).Rel a b ↔
      (refineOnBlock (data.vertexPartition wall) (data.edgePartition (star.edge 0))
        anchor.1 (star.edgePartition_refines_wall data 0)).Rel a b := by
  have hReprRel : (data.vertexPartition wall).Rel anchor.1
      ((data.vertexPartition wall).repr a) :=
    hA.trans ((data.vertexPartition wall).rel_repr_right a)
  have hSelected := candidate_resolution_anchorBlock setup _ hReprRel
  show ((cand).datum.vertexPartition (freshVertex target)).Rel a b ↔ _
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_fresh]
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).right)
    (fun blk ↦ ((cand).contracts blk).right_refines) a b) ?_
  rw [hSelected]
  rfl

/-- Above the new leaf an ordinary block is split into singletons. -/
theorem leafPartition_rel_ordinary {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition (oldVertex target wall)).Rel a b ↔ a = b := by
  have hBackground := candidate_resolution_of_not_wall_rel setup
    ((data.vertexPartition wall).repr a) (not_rel_repr hA)
  show ((cand).datum.vertexPartition (oldVertex target wall)).Rel a b ↔ _
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_old_wall]
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).left)
    (fun blk ↦ ((cand).contracts blk).left_refines) a b) ?_
  rw [hBackground]
  exact (data.vertexPartition wall).splitBlock_rel_of_rel_anchor_iff
    ((data.vertexPartition wall).repr a) a ((data.vertexPartition wall).rel_repr_left a) b

/-- Above the new trivalent point an ordinary block is kept whole. -/
theorem branchPartition_rel_ordinary {a b : Fin degree}
    (hA : ¬ (data.vertexPartition wall).Rel anchor.1 a) :
    ((cand).datum.vertexPartition (freshVertex target)).Rel a b ↔
      (data.vertexPartition wall).Rel a b := by
  have hBackground := candidate_resolution_of_not_wall_rel setup
    ((data.vertexPartition wall).repr a) (not_rel_repr hA)
  show ((cand).datum.vertexPartition (freshVertex target)).Rel a b ↔ _
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_fresh]
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).right)
    (fun blk ↦ ((cand).contracts blk).right_refines) a b) ?_
  rw [hBackground]
  exact Iff.rfl

/-- **The Base I new-edge partition is discrete**: every sheet of the source
carries its own occurrence over `t_1`, of index one. -/
theorem newEdge_rel_iff (a b : Fin degree) :
    (LocalResolution.paste (data.vertexPartition wall) (cand).resolution
        (cand).contracts).newEdge.Rel a b ↔ a = b := by
  refine Iff.trans (SheetPartition.paste_rel_iff (data.vertexPartition wall)
    (fun blk ↦ ((cand).resolution blk).newEdge)
    (fun blk ↦ ((cand).resolution blk).edge_refines_left.trans
      ((cand).contracts blk).left_refines) a b) ?_
  by_cases hA : (data.vertexPartition wall).Rel anchor.1 a
  · have hReprRel : (data.vertexPartition wall).Rel anchor.1
        ((data.vertexPartition wall).repr a) :=
      hA.trans ((data.vertexPartition wall).rel_repr_right a)
    rw [candidate_resolution_anchorBlock setup _ hReprRel]
    exact (data.vertexPartition wall).splitBlock_rel_of_rel_anchor_iff anchor.1 a hA b
  · rw [candidate_resolution_of_not_wall_rel setup _ (not_rel_repr hA)]
    exact (data.vertexPartition wall).splitBlock_rel_of_rel_anchor_iff
      ((data.vertexPartition wall).repr a) a
      ((data.vertexPartition wall).rel_repr_left a) b

theorem newSourceEdge_eq_iff (a b : Fin degree) :
    (cand).newSourceEdge a = (cand).newSourceEdge b ↔ a = b := by
  constructor
  · intro hEq
    refine (newEdge_rel_iff setup a b).mp ?_
    exact congrArg (fun edge : (cand).datum.SourceEdge ↦ edge.1.2) hEq
  · rintro rfl
    rfl

theorem newSourceEdge_injective :
    Function.Injective (fun sheet : Fin degree ↦ (cand).newSourceEdge sheet) :=
  fun _ _ h ↦ (newSourceEdge_eq_iff setup _ _).mp h

theorem newSourceEdge_ne_oldSourceEdge (s : Fin degree) (old : data.SourceEdge) :
    (cand).newSourceEdge s ≠ (cand).oldSourceEdge old := by
  intro hEq
  have h := congrArg (fun edge : (cand).datum.SourceEdge ↦ edge.1.1) hEq
  have hNone := (occurrenceEquiv target wall (cand).right).injective h
  cases hNone

/-! ## 4.  Incidence at the two new endpoint layers

The Base I base tree `T_\u2205` sends **both** old occurrences to the new
trivalent point `v` (`leafAssignment`), so no old occurrence at all meets a
vertex above the new leaf `u`.  Every vertex above `u` therefore sees only new
occurrences over `t\u2081`. -/

theorem candidate_right_apply (edge : target.edges) : (cand).right edge = true := rfl

/-- Target-level incidence of an old occurrence at the leaf layer: it never
happens, because `leafAssignment` sends every old occurrence to the branch
layer. -/
theorem mem_incidentEdges_leaf_old (edge : target.edges) :
    occurrenceEquiv target wall (cand).right (some edge) ∈
        GluingDatum.incidentEdges (oldVertex target wall) ↔
      (edge ∈ GluingDatum.incidentEdges wall ∧ (cand).right edge = false) := by
  constructor
  · intro hMem
    have hCases := (GluingContraction.mem_incidentEdges_iff (oldVertex target wall)
      (occurrenceEquiv target wall (cand).right (some edge))).mp hMem
    rw [occurrenceEquiv_some] at hCases
    obtain ⟨hAt, hSide⟩ :=
      (oldEnds_incident_oldVertex_iff target wall (cand).right edge).mp hCases
    exact ⟨(GluingContraction.mem_incidentEdges_iff wall edge).mpr hAt, hSide⟩
  · rintro ⟨hAt, hSide⟩
    refine (GluingContraction.mem_incidentEdges_iff (oldVertex target wall)
      (occurrenceEquiv target wall (cand).right (some edge))).mpr ?_
    rw [occurrenceEquiv_some]
    exact (oldEnds_incident_oldVertex_iff target wall (cand).right edge).mpr
      ⟨(GluingContraction.mem_incidentEdges_iff wall edge).mp hAt, hSide⟩

theorem mem_incidentEdges_branch_old (edge : target.edges) :
    occurrenceEquiv target wall (cand).right (some edge) ∈
        GluingDatum.incidentEdges (freshVertex target) ↔
      (edge ∈ GluingDatum.incidentEdges wall ∧ (cand).right edge = true) := by
  constructor
  · intro hMem
    have hCases := (GluingContraction.mem_incidentEdges_iff (freshVertex target)
      (occurrenceEquiv target wall (cand).right (some edge))).mp hMem
    rw [occurrenceEquiv_some] at hCases
    obtain ⟨hAt, hSide⟩ :=
      (oldEnds_incident_freshVertex_iff target wall (cand).right edge).mp hCases
    exact ⟨(GluingContraction.mem_incidentEdges_iff wall edge).mpr hAt, hSide⟩
  · rintro ⟨hAt, hSide⟩
    refine (GluingContraction.mem_incidentEdges_iff (freshVertex target)
      (occurrenceEquiv target wall (cand).right (some edge))).mpr ?_
    rw [occurrenceEquiv_some]
    exact (oldEnds_incident_freshVertex_iff target wall (cand).right edge).mpr
      ⟨(GluingContraction.mem_incidentEdges_iff wall edge).mp hAt, hSide⟩

/-- No old occurrence reaches the leaf layer. -/
theorem not_incident_oldSourceEdge_leafVertex (x : Fin degree) (old : data.SourceEdge) :
    ¬ Incident (cand).datum ((cand).oldSourceEdge old) (leafVertex setup x) := by
  intro hIncident
  have hMem := ((incident_iff_target_mem_and_rel _ _ _).mp hIncident).1
  rw [BalancedGlobal.Candidate.oldSourceEdge_target] at hMem
  have hTarget : occurrenceEquiv target wall (cand).right (some old.1.1) ∈
      GluingDatum.incidentEdges (oldVertex target wall) := hMem
  have hFalse : (cand).right old.1.1 = false :=
    ((mem_incidentEdges_leaf_old setup old.1.1).mp hTarget).2
  rw [candidate_right_apply setup old.1.1] at hFalse
  exact Bool.noConfusion hFalse

/-- An old occurrence at the wall reaches the branch layer at its own sheet. -/
theorem oldSourceEdge_incident_branchVertex (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) (sheet : Fin degree) :
    Incident (cand).datum ((cand).oldSourceEdge (data.sourceEdge edge sheet))
      (branchVertex setup sheet) :=
  M11SplitSurvival.oldSourceEdge_incident_fresh (cand) edge hAt
    (candidate_right_apply setup edge) sheet

/-- Membership form of incidence at a leaf-layer vertex. -/
theorem incident_leafVertex_iff (x : Fin degree) (e : (cand).datum.SourceEdge) :
    Incident (cand).datum e (leafVertex setup x) ↔
      (e.1.1 ∈ GluingDatum.incidentEdges (oldVertex target wall) ∧
        ((cand).datum.vertexPartition (oldVertex target wall)).Rel x e.1.2) := by
  constructor
  · intro hIncident
    obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
    exact ⟨hMem, Eq.trans (((cand).datum.vertexPartition
      (oldVertex target wall)).rel_repr_right x) hRel⟩
  · rintro ⟨hMem, hRel⟩
    refine (incident_iff_target_mem_and_rel _ _ _).mpr ⟨hMem, ?_⟩
    exact Eq.trans (((cand).datum.vertexPartition
      (oldVertex target wall)).rel_repr_right x).symm hRel

/-- Membership form of incidence at a branch-layer vertex. -/
theorem incident_branchVertex_iff (x : Fin degree) (e : (cand).datum.SourceEdge) :
    Incident (cand).datum e (branchVertex setup x) ↔
      (e.1.1 ∈ GluingDatum.incidentEdges (freshVertex target) ∧
        ((cand).datum.vertexPartition (freshVertex target)).Rel x e.1.2) := by
  constructor
  · intro hIncident
    obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
    exact ⟨hMem, Eq.trans (((cand).datum.vertexPartition
      (freshVertex target)).rel_repr_right x) hRel⟩
  · rintro ⟨hMem, hRel⟩
    refine (incident_iff_target_mem_and_rel _ _ _).mpr ⟨hMem, ?_⟩
    exact Eq.trans (((cand).datum.vertexPartition
      (freshVertex target)).rel_repr_right x).symm hRel

/-- The new occurrence of a sheet is named by that very sheet: the Base I
new-edge partition is discrete. -/
theorem newSourceEdge_sheet (y : Fin degree) : ((cand).newSourceEdge y).1.2 = y :=
  ((newEdge_rel_iff setup y ((cand).newSourceEdge y).1.2).mp
    ((LocalResolution.paste (data.vertexPartition wall) (cand).resolution
      (cand).contracts).newEdge.rel_repr_right y)).symm

/-! ## 5.  The leaf layer: one fold, and singletons everywhere else -/

theorem leafVertex_eq {a b : Fin degree}
    (hRel : ((cand).datum.vertexPartition (oldVertex target wall)).Rel a b) :
    leafVertex setup a = leafVertex setup b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hRel

theorem branchVertex_eq {a b : Fin degree}
    (hRel : ((cand).datum.vertexPartition (freshVertex target)).Rel a b) :
    branchVertex setup a = branchVertex setup b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hRel

theorem branchPartition_rel_of_branchVertex_eq {a b : Fin degree}
    (hEq : branchVertex setup a = branchVertex setup b) :
    ((cand).datum.vertexPartition (freshVertex target)).Rel a b :=
  congrArg (fun v : (cand).datum.SourceVertex ↦ v.1.2) hEq

/-- Away from the fold every sheet is alone above the new leaf. -/
theorem leafPartition_rel_singleton {y : Fin degree}
    (hFirst : y ≠ setup.foldFirst) (hSecond : y ≠ setup.foldSecond) (z : Fin degree) :
    ((cand).datum.vertexPartition (oldVertex target wall)).Rel y z ↔ y = z := by
  by_cases hY : (data.vertexPartition wall).Rel anchor.1 y
  · rw [leafPartition_rel_anchor setup hY]
    exact pairBlock_rel_iff_of_ne (data.vertexPartition wall) setup.foldFirst
      setup.foldSecond y z setup.foldFirst_ne_foldSecond
      (setup.foldFirst_wall.symm.trans setup.foldSecond_wall)
      (setup.foldFirst_wall.symm.trans hY) hFirst hSecond
  · exact leafPartition_rel_ordinary setup hY

/-- **The fold `F`**: above the new leaf the anchor keeps exactly the two-sheet
class `{A', A''}`. -/
theorem leafPartition_rel_fold (z : Fin degree) :
    ((cand).datum.vertexPartition (oldVertex target wall)).Rel setup.foldFirst z ↔
      z = setup.foldFirst ∨ z = setup.foldSecond := by
  rw [leafPartition_rel_anchor setup setup.foldFirst_wall]
  exact (data.vertexPartition wall).pairBlock_rel_first_iff setup.foldFirst
    setup.foldSecond z setup.foldFirst_ne_foldSecond
    (setup.foldFirst_wall.symm.trans setup.foldSecond_wall)

theorem leafVertex_fold_eq :
    leafVertex setup setup.foldSecond = leafVertex setup setup.foldFirst :=
  (leafVertex_eq setup ((leafPartition_rel_fold setup setup.foldSecond).mpr
    (Or.inr rfl))).symm

/-- Every surviving occurrence at a leaf-layer vertex is a new occurrence. -/
theorem exists_newSourceEdge_of_incident_leafVertex (x : Fin degree)
    {e : (cand).datum.SourceEdge} (hIncident : Incident (cand).datum e (leafVertex setup x)) :
    ∃ y, e = (cand).newSourceEdge y ∧
      ((cand).datum.vertexPartition (oldVertex target wall)).Rel x y := by
  rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, hOld⟩ | ⟨y, hNew⟩
  · exact absurd (hOld ▸ hIncident) (not_incident_oldSourceEdge_leafVertex setup x old)
  · refine ⟨y, hNew, ?_⟩
    have hRel := ((incident_leafVertex_iff setup x e).mp hIncident).2
    rw [hNew, newSourceEdge_sheet setup y] at hRel
    exact hRel

theorem nonDanglingIncident_leafVertex_singleton_subset {x : Fin degree}
    (hFirst : x ≠ setup.foldFirst) (hSecond : x ≠ setup.foldSecond) :
    nonDanglingIncident (cand).datum (leafVertex setup x) ⊆
      {(cand).newSourceEdge x} := by
  intro e hMem
  obtain ⟨-, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  obtain ⟨y, hY, hRel⟩ := exists_newSourceEdge_of_incident_leafVertex setup x hIncident
  rw [Finset.mem_singleton, hY,
    (leafPartition_rel_singleton setup hFirst hSecond y).mp hRel]

/-- **`nd = 0` at every singleton above the new leaf.**  Those blocks carry one
dangling occurrence each. -/
theorem nonDanglingValency_leafVertex_singleton (hValid : data.Valid) {x : Fin degree}
    (hFirst : x ≠ setup.foldFirst) (hSecond : x ≠ setup.foldSecond) :
    nonDanglingValency (cand).datum (leafVertex setup x) = 0 := by
  classical
  have hLe : nonDanglingValency (cand).datum (leafVertex setup x) ≤ 1 := by
    rw [← card_nonDanglingIncident]
    exact le_trans (Finset.card_le_card
      (nonDanglingIncident_leafVertex_singleton_subset setup hFirst hSecond))
      (le_of_eq (Finset.card_singleton _))
  have hNe := NonDanglingValency.nonDanglingValency_ne_one (cand).datum
    (validCandidate_datum_valid setup hValid).1 (leafVertex setup x)
  omega

/-- The new occurrence of a singleton sheet dangles: its end above `u` is a
leaf of the outgoing source. -/
theorem newSourceEdge_isDangling_of_ne_fold (hValid : data.Valid) {x : Fin degree}
    (hFirst : x ≠ setup.foldFirst) (hSecond : x ≠ setup.foldSecond) :
    IsDangling (cand).datum ((cand).newSourceEdge x) :=
  (DanglingSideStructure.nonDanglingValency_eq_zero_iff (cand).datum
      (leafVertex setup x)).mp
    (nonDanglingValency_leafVertex_singleton setup hValid hFirst hSecond)
    ((cand).newSourceEdge x) (bridgeEdge_incident_leaf setup x)

/-! ## 6.  The two vertices above the new branch point, and the surviving fold -/

/-- The literal source occurrence named by an incident survivor. -/
theorem sourceEdge_occurrenceSheet {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    data.sourceEdge (star.edge label) (occurrenceSheet edge) = edge.1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact (survivor_target hEdge).symm
  · show (data.edgePartition (star.edge label)).repr (occurrenceSheet edge) =
      occurrenceSheet edge
    exact survivor_repr hEdge

theorem survivor_not_isDangling {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    ¬ IsDangling data edge.1 :=
  (mem_survivors data anchor edge).mp
    ((mem_directionSurvivors data star anchor label edge).mp hEdge).1

theorem retained_survivor_survives (hValid : data.Valid) {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    ¬ IsDangling (cand).datum ((cand).oldSourceEdge edge.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ hValid.1 _
    (survivor_not_isDangling hEdge)

/-- Every survivor at the anchor reaches the branch-layer vertex of its own
sheet: the Base I base tree keeps both old occurrences at `v`. -/
theorem survivor_incident_branchVertex {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    Incident (cand).datum ((cand).oldSourceEdge edge.1)
      (branchVertex setup (occurrenceSheet edge)) := by
  have h := oldSourceEdge_incident_branchVertex setup (star.edge label)
    (star.edge_mem_incidentEdges label) (occurrenceSheet edge)
  rwa [sourceEdge_occurrenceSheet hEdge] at h

theorem nonDanglingValency_branchVertex_ne_zero (hValid : data.Valid) {label : Fin 2}
    {edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hEdge : edge ∈ directionSurvivors data star anchor label) :
    nonDanglingValency (cand).datum (branchVertex setup (occurrenceSheet edge)) ≠ 0 :=
  ClassInjectivity.nonDanglingValency_ne_zero_of_incident _
    (retained_survivor_survives setup hValid hEdge)
    (survivor_incident_branchVertex setup hEdge)

theorem candidate_right_partition_anchor :
    ((validCandidate setup).resolution anchor.1).right =
      refineOnBlock (data.vertexPartition wall) (data.edgePartition (star.edge 0))
        anchor.1 (star.edgePartition_refines_wall data 0) := by
  rw [validCandidate_resolution_anchor setup]
  exact selectedResolution_right setup

/-- **`A₁ ≠ A₂`**: the two classes above the new branch point are distinct. -/
theorem branchVertex_fold_ne :
    branchVertex setup setup.foldFirst ≠ branchVertex setup setup.foldSecond := by
  intro hEq
  have hRel := branchPartition_rel_of_branchVertex_eq setup hEq
  rw [branchPartition_rel_anchor setup setup.foldFirst_wall] at hRel
  have hNot := branch_not_rel setup
  rw [candidate_right_partition_anchor setup] at hNot
  exact hNot hRel

/-- **The fold's first occurrence survives.**  Its own leaf end is divalent, so
the criterion runs through the fold's *other* occurrence, which reaches the
second vertex above the branch point. -/
theorem newSourceEdge_foldFirst_survives (hValid : data.Valid) :
    ¬ IsDangling (cand).datum ((cand).newSourceEdge setup.foldFirst) := by
  refine not_isDangling_of_third (cand).datum ((cand).newSourceEdge setup.foldFirst)
    ((cand).newSourceEdge setup.foldSecond)
    (p := leafVertex setup setup.foldFirst) (q := branchVertex setup setup.foldFirst)
    (r := branchVertex setup setup.foldSecond) (sourceEnds_bridgeEdge setup _) ?_ ?_ ?_ ?_
  · have hEnds : (cand).datum.sourceEnds ((cand).newSourceEdge setup.foldSecond) =
        (leafVertex setup setup.foldSecond, branchVertex setup setup.foldSecond) :=
      sourceEnds_bridgeEdge setup setup.foldSecond
    rw [hEnds, leafVertex_fold_eq setup]
  · exact (branchVertex_fold_ne setup).symm
  · exact nonDanglingValency_branchVertex_ne_zero setup hValid (setup.firstOf_mem 0)
  · exact nonDanglingValency_branchVertex_ne_zero setup hValid (setup.secondOf_mem 0)

theorem newSourceEdge_foldSecond_survives (hValid : data.Valid) :
    ¬ IsDangling (cand).datum ((cand).newSourceEdge setup.foldSecond) := by
  refine not_isDangling_of_third (cand).datum ((cand).newSourceEdge setup.foldSecond)
    ((cand).newSourceEdge setup.foldFirst)
    (p := leafVertex setup setup.foldSecond) (q := branchVertex setup setup.foldSecond)
    (r := branchVertex setup setup.foldFirst) (sourceEnds_bridgeEdge setup _) ?_ ?_ ?_ ?_
  · have hEnds : (cand).datum.sourceEnds ((cand).newSourceEdge setup.foldFirst) =
        (leafVertex setup setup.foldFirst, branchVertex setup setup.foldFirst) :=
      sourceEnds_bridgeEdge setup setup.foldFirst
    rw [hEnds, ← leafVertex_fold_eq setup]
  · exact branchVertex_fold_ne setup
  · exact nonDanglingValency_branchVertex_ne_zero setup hValid (setup.secondOf_mem 0)
  · exact nonDanglingValency_branchVertex_ne_zero setup hValid (setup.firstOf_mem 0)

/-- **Exactly the two fold occurrences over `t₁` survive.** -/
theorem newSourceEdge_survives_iff (hValid : data.Valid) (y : Fin degree) :
    ¬ IsDangling (cand).datum ((cand).newSourceEdge y) ↔
      (y = setup.foldFirst ∨ y = setup.foldSecond) := by
  constructor
  · intro hSurvives
    by_cases hF : y = setup.foldFirst
    · exact Or.inl hF
    · by_cases hS : y = setup.foldSecond
      · exact Or.inr hS
      · exact absurd (newSourceEdge_isDangling_of_ne_fold setup hValid hF hS) hSurvives
  · rintro (rfl | rfl)
    · exact newSourceEdge_foldFirst_survives setup hValid
    · exact newSourceEdge_foldSecond_survives setup hValid

/-! ## 7.  The fold's exact star: `nd(F) = 2` -/

/-- **The exact surviving star of the fold `F`**: the two bridge occurrences,
and nothing else. -/
theorem nonDanglingIncident_leafVertex_fold (hValid : data.Valid) :
    nonDanglingIncident (cand).datum (leafVertex setup setup.foldFirst) =
      {(cand).newSourceEdge setup.foldFirst, (cand).newSourceEdge setup.foldSecond} := by
  classical
  ext e
  rw [mem_nonDanglingIncident, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hIncident⟩
    obtain ⟨y, hY, hRel⟩ :=
      exists_newSourceEdge_of_incident_leafVertex setup setup.foldFirst hIncident
    rcases (leafPartition_rel_fold setup y).mp hRel with hCase | hCase
    · exact Or.inl (by rw [hY, hCase])
    · exact Or.inr (by rw [hY, hCase])
  · rintro (rfl | rfl)
    · exact ⟨newSourceEdge_foldFirst_survives setup hValid,
        bridgeEdge_incident_leaf setup setup.foldFirst⟩
    · refine ⟨newSourceEdge_foldSecond_survives setup hValid, ?_⟩
      rw [← leafVertex_fold_eq setup]
      exact bridgeEdge_incident_leaf setup setup.foldSecond

/-- **`nd(F) = 2`**: the fold above the new leaf is an interior vertex of the
bridge row, not a branch vertex. -/
theorem nonDanglingValency_leafVertex_fold (hValid : data.Valid) :
    nonDanglingValency (cand).datum (leafVertex setup setup.foldFirst) = 2 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_leafVertex_fold setup hValid,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact fun hEq ↦ setup.foldFirst_ne_foldSecond
        ((newSourceEdge_eq_iff setup _ _).mp hEq)), Finset.card_singleton]

/-! ## 8.  The two branch vertices `A₁`, `A₂`: `nd = 3` -/

include setup in
/-- Inside the anchor the `t₃`-classes are the `t₂`-classes, in relational
form. -/
theorem thin_rel_iff {a b : Fin degree}
    (hA : (data.vertexPartition wall).Rel anchor.1 a) :
    (data.edgePartition (star.edge 1)).Rel a b ↔
      (data.edgePartition (star.edge 0)).Rel a b := by
  constructor
  · intro hRel
    have hMem : b ∈ (data.edgePartition (star.edge 1)).block a :=
      (SheetPartition.mem_block_iff _ _ _).mpr hRel
    rw [thin_block_eq setup hA] at hMem
    exact (SheetPartition.mem_block_iff _ _ _).mp hMem
  · intro hRel
    have hMem : b ∈ (data.edgePartition (star.edge 0)).block a :=
      (SheetPartition.mem_block_iff _ _ _).mpr hRel
    rw [← thin_block_eq setup hA] at hMem
    exact (SheetPartition.mem_block_iff _ _ _).mp hMem

theorem occurrenceSheet_thick_fold
    {thick : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hThick : thick ∈ directionSurvivors data star anchor 0) :
    occurrenceSheet thick = setup.foldFirst ∨ occurrenceSheet thick = setup.foldSecond := by
  classical
  have hMem := hThick
  rw [setup.directionSurvivors_eq 0, Finset.mem_insert, Finset.mem_singleton] at hMem
  rcases hMem with hCase | hCase
  · exact Or.inl (congrArg occurrenceSheet hCase)
  · exact Or.inr (congrArg occurrenceSheet hCase)

theorem not_rel_fold :
    ¬ (data.edgePartition (star.edge 0)).Rel setup.foldFirst setup.foldSecond :=
  not_rel_occurrenceSheet (setup.firstOf_mem 0) (setup.secondOf_mem 0)
    (setup.firstOf_ne_secondOf 0)

/-- Two fold sheets in one `t₂`-class are equal: `A₁` and `A₂` are distinct
classes. -/
theorem fold_eq_of_rel {y z : Fin degree}
    (hY : y = setup.foldFirst ∨ y = setup.foldSecond)
    (hZ : z = setup.foldFirst ∨ z = setup.foldSecond)
    (hRel : (data.edgePartition (star.edge 0)).Rel y z) : y = z := by
  rcases hY with rfl | rfl <;> rcases hZ with rfl | rfl
  · rfl
  · exact absurd hRel (not_rel_fold setup)
  · exact absurd hRel.symm (not_rel_fold setup)
  · rfl

/-- A surviving old occurrence of a named direction whose sheet lies in the
anchor block is one of that direction's survivors. -/
theorem exists_directionSurvivor_eq (label : Fin 2) (old : data.SourceEdge)
    (hTarget : old.1.1 = star.edge label)
    (hWall : (data.vertexPartition wall).Rel anchor.1 old.1.2)
    (hSurvives : ¬ IsDangling data old) :
    ∃ edge ∈ directionSurvivors data star anchor label, edge.1 = old := by
  have hIncident : Incident data old (WallBlock.sourceVertex data wall anchor) := by
    refine (incident_wallBlock_sourceVertex_iff data anchor old).mpr
      ⟨hTarget ▸ star.edge_mem_incidentEdges label, ?_⟩
    apply Subtype.ext
    change (data.vertexPartition wall).repr old.1.2 = anchor.1
    unfold SheetPartition.Rel at hWall
    rw [← hWall, anchor.2]
  refine ⟨⟨old, hIncident⟩, ?_, rfl⟩
  exact (mem_directionSurvivors data star anchor label _).mpr
    ⟨(mem_survivors data anchor _).mpr hSurvives, hTarget⟩

include setup in
/-- Each sheet of the anchor meets a `t₃`-survivor, through the alignment. -/
theorem exists_thinPartner {s : Fin degree}
    (hS : (data.vertexPartition wall).Rel anchor.1 s) :
    ∃ thin ∈ directionSurvivors data star anchor 1,
      (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thin) s := by
  classical
  have hMem : s ∈ (data.vertexPartition wall).block anchor.1 :=
    ((data.vertexPartition wall).mem_block_iff _ _).mpr hS
  rw [← biUnion_block_eq_wallBlock setup.anchor_source 1] at hMem
  obtain ⟨thin, hThin, hBlock⟩ := Finset.mem_biUnion.mp hMem
  refine ⟨thin, hThin, ?_⟩
  exact (thin_rel_iff setup (occurrenceSheet_wall_rel thin)).mp
    ((SheetPartition.mem_block_iff _ _ _).mp hBlock)

/-- **The exact surviving star of a vertex above the new branch point**: the
bridge occurrence of its own fold sheet, plus the two survivors of its cross
pair.  Nothing else: the other `k-1` new occurrences of the class dangle,
because their ends above `u` are singleton leaves. -/
theorem mem_nonDanglingIncident_branchVertex_anchor (hValid : data.Valid)
    {thick thin : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hThick : thick ∈ directionSurvivors data star anchor 0)
    (hThin : thin ∈ directionSurvivors data star anchor 1)
    (hMeet : (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thick)
      (occurrenceSheet thin)) (e : (cand).datum.SourceEdge) :
    e ∈ nonDanglingIncident (cand).datum (branchVertex setup (occurrenceSheet thick)) ↔
      (e = (cand).newSourceEdge (occurrenceSheet thick) ∨
        e = (cand).oldSourceEdge thick.1 ∨ e = (cand).oldSourceEdge thin.1) := by
  classical
  have hWallThick : (data.vertexPartition wall).Rel anchor.1 (occurrenceSheet thick) :=
    occurrenceSheet_wall_rel thick
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨y, rfl⟩
    · have hOldSurv : ¬ IsDangling data old := fun h ↦ hSurvives
        ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
          (candidate_sourceGenus setup) old).mpr h)
      obtain ⟨hTargetMem, hRel⟩ := (incident_branchVertex_iff setup _ _).mp hIncident
      rw [BalancedGlobal.Candidate.oldSourceEdge_target] at hTargetMem
      have hAt : old.1.1 ∈ GluingDatum.incidentEdges wall :=
        ((mem_incidentEdges_branch_old setup old.1.1).mp hTargetMem).1
      rw [BalancedGlobal.Candidate.oldSourceEdge_sheet,
        branchPartition_rel_anchor setup hWallThick,
        refineOnBlock_rel_iff (data.vertexPartition wall)
          (data.edgePartition (star.edge 0)) anchor.1 (occurrenceSheet thick) old.1.2
          (star.edgePartition_refines_wall data 0) hWallThick] at hRel
      have hWallOld : (data.vertexPartition wall).Rel anchor.1 old.1.2 :=
        hWallThick.trans ((star.edgePartition_refines_wall data 0).rel hRel)
      rw [incidentEdges_eq_star_pair star, Finset.mem_insert,
        Finset.mem_singleton] at hAt
      rcases hAt with hCase | hCase
      · obtain ⟨edge, hEdge, hEq⟩ :=
          exists_directionSurvivor_eq 0 old hCase hWallOld hOldSurv
        have hSheet : occurrenceSheet edge = old.1.2 :=
          congrArg (fun x : data.SourceEdge ↦ x.1.2) hEq
        have hSame : occurrenceSheet thick = occurrenceSheet edge := by
          refine fold_eq_of_rel setup (occurrenceSheet_thick_fold setup hThick)
            (occurrenceSheet_thick_fold setup hEdge) ?_
          rw [hSheet]
          exact hRel
        rw [← hEq, eq_of_occurrenceSheet_eq hThick hEdge hSame]
        exact Or.inr (Or.inl rfl)
      · obtain ⟨edge, hEdge, hEq⟩ :=
          exists_directionSurvivor_eq 1 old hCase hWallOld hOldSurv
        have hSheet : occurrenceSheet edge = old.1.2 :=
          congrArg (fun x : data.SourceEdge ↦ x.1.2) hEq
        have hRelThin : (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thin)
            (occurrenceSheet edge) := by
          rw [hSheet]
          exact hMeet.symm.trans hRel
        have hSame : thin = edge := by
          by_contra hNe
          exact not_rel_occurrenceSheet hThin hEdge hNe
            ((thin_rel_iff setup (occurrenceSheet_wall_rel thin)).mpr hRelThin)
        rw [← hEq, ← hSame]
        exact Or.inr (Or.inr rfl)
    · have hFoldY := (newSourceEdge_survives_iff setup hValid y).mp hSurvives
      obtain ⟨-, hRel⟩ := (incident_branchVertex_iff setup _ _).mp hIncident
      rw [newSourceEdge_sheet setup y, branchPartition_rel_anchor setup hWallThick,
        refineOnBlock_rel_iff (data.vertexPartition wall)
          (data.edgePartition (star.edge 0)) anchor.1 (occurrenceSheet thick) y
          (star.edgePartition_refines_wall data 0) hWallThick] at hRel
      exact Or.inl (congrArg (cand).newSourceEdge
        (fold_eq_of_rel setup (occurrenceSheet_thick_fold setup hThick) hFoldY hRel).symm)
  · rintro (rfl | rfl | rfl)
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨(newSourceEdge_survives_iff setup hValid _).mpr
          (occurrenceSheet_thick_fold setup hThick),
          bridgeEdge_incident_branch setup (occurrenceSheet thick)⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨retained_survivor_survives setup hValid hThick,
          survivor_incident_branchVertex setup hThick⟩
    · refine (mem_nonDanglingIncident _ _ _).mpr
        ⟨retained_survivor_survives setup hValid hThin, ?_⟩
      have hVertex : branchVertex setup (occurrenceSheet thin) =
          branchVertex setup (occurrenceSheet thick) :=
        branchVertex_eq setup ((branchPartition_rel_anchor setup
          (occurrenceSheet_wall_rel thin)).mpr
          ((refineOnBlock_rel_iff (data.vertexPartition wall)
            (data.edgePartition (star.edge 0)) anchor.1 (occurrenceSheet thin)
            (occurrenceSheet thick) (star.edgePartition_refines_wall data 0)
            (occurrenceSheet_wall_rel thin)).mpr hMeet.symm))
      rw [← hVertex]
      exact survivor_incident_branchVertex setup hThin

theorem nonDanglingIncident_branchVertex_anchor (hValid : data.Valid)
    {thick thin : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hThick : thick ∈ directionSurvivors data star anchor 0)
    (hThin : thin ∈ directionSurvivors data star anchor 1)
    (hMeet : (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thick)
      (occurrenceSheet thin)) :
    nonDanglingIncident (cand).datum (branchVertex setup (occurrenceSheet thick)) =
      {(cand).newSourceEdge (occurrenceSheet thick), (cand).oldSourceEdge thick.1,
        (cand).oldSourceEdge thin.1} := by
  classical
  ext e
  rw [mem_nonDanglingIncident_branchVertex_anchor setup hValid hThick hThin hMeet e,
    Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]

theorem oldSourceEdge_cross_ne
    {thick thin : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hThick : thick ∈ directionSurvivors data star anchor 0)
    (hThin : thin ∈ directionSurvivors data star anchor 1) :
    (cand).oldSourceEdge thick.1 ≠ (cand).oldSourceEdge thin.1 := by
  intro hEq
  have hSame := ResolutionCut.oldSourceEdge_injective (cand) hEq
  have hZero : thick.1.1.1 = star.edge 0 := survivor_target hThick
  have hOne : thin.1.1.1 = star.edge 1 := survivor_target hThin
  rw [hSame, hOne] at hZero
  exact star.edge_injective.ne (by decide : (1 : Fin 2) ≠ 0) hZero

/-- **`nd(A_i) = 3`**: the bridge occurrence plus the two survivors of the
cross pair. -/
theorem nonDanglingValency_branchVertex_anchor (hValid : data.Valid)
    {thick thin : IncidentSourceEdge data (WallBlock.sourceVertex data wall anchor)}
    (hThick : thick ∈ directionSurvivors data star anchor 0)
    (hThin : thin ∈ directionSurvivors data star anchor 1)
    (hMeet : (data.edgePartition (star.edge 0)).Rel (occurrenceSheet thick)
      (occurrenceSheet thin)) :
    nonDanglingValency (cand).datum
      (branchVertex setup (occurrenceSheet thick)) = 3 := by
  classical
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_branchVertex_anchor setup hValid hThick hThin hMeet,
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq)
      · exact newSourceEdge_ne_oldSourceEdge setup _ _ hEq
      · exact newSourceEdge_ne_oldSourceEdge setup _ _ hEq),
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact oldSourceEdge_cross_ne setup hThick hThin), Finset.card_singleton]

/-! ## 9.  The ordinary wall blocks: nothing is split or joined -/

theorem incident_sourceEndpoint_wall_iff (x : Fin degree) (old : data.SourceEdge) :
    Incident data old (data.sourceEndpoint wall x) ↔
      (old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        (data.vertexPartition wall).Rel x old.1.2) := by
  constructor
  · intro hIncident
    obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel _ _ _).mp hIncident
    exact ⟨hMem, Eq.trans ((data.vertexPartition wall).rel_repr_right x) hRel⟩
  · rintro ⟨hMem, hRel⟩
    exact (incident_iff_target_mem_and_rel _ _ _).mpr
      ⟨hMem, Eq.trans ((data.vertexPartition wall).rel_repr_right x).symm hRel⟩

theorem incident_oldSourceEdge_branchVertex_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) (old : data.SourceEdge) :
    Incident (cand).datum ((cand).oldSourceEdge old) (branchVertex setup x) ↔
      Incident data old (data.sourceEndpoint wall x) := by
  rw [incident_branchVertex_iff, BalancedGlobal.Candidate.oldSourceEdge_target,
    mem_incidentEdges_branch_old, BalancedGlobal.Candidate.oldSourceEdge_sheet,
    branchPartition_rel_ordinary setup hX, incident_sourceEndpoint_wall_iff]
  have hRight : (cand).right old.1.1 = true := candidate_right_apply setup old.1.1
  simp only [hRight, and_true]

theorem ne_foldFirst_of_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) : x ≠ setup.foldFirst := by
  rintro rfl
  exact hX setup.foldFirst_wall

theorem ne_foldSecond_of_ordinary {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) : x ≠ setup.foldSecond := by
  rintro rfl
  exact hX setup.foldSecond_wall

/-- **`nd = 0` above the new leaf at every ordinary block.** -/
theorem nonDanglingValency_leafVertex_ordinary (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingValency (cand).datum (leafVertex setup x) = 0 :=
  nonDanglingValency_leafVertex_singleton setup hValid
    (ne_foldFirst_of_ordinary setup hX) (ne_foldSecond_of_ordinary setup hX)

/-- **The ordinary-block census.**  Above the new branch point an ordinary
block keeps exactly its old surviving star: every new occurrence there is
dangling, because its end above `u` is a singleton leaf. -/
theorem nonDanglingIncident_branchVertex_ordinary (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingIncident (cand).datum (branchVertex setup x) =
      (nonDanglingIncident data (data.sourceEndpoint wall x)).image (cand).oldSourceEdge := by
  classical
  ext e
  rw [mem_nonDanglingIncident, Finset.mem_image]
  constructor
  · rintro ⟨hSurvives, hIncident⟩
    rcases ResolutionPruning.sourceEdge_cases (cand) e with ⟨old, rfl⟩ | ⟨y, rfl⟩
    · refine ⟨old, (mem_nonDanglingIncident _ _ _).mpr ⟨?_, ?_⟩, rfl⟩
      · exact fun h ↦ hSurvives ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand)
          hValid (candidate_sourceGenus setup) old).mpr h)
      · exact (incident_oldSourceEdge_branchVertex_ordinary setup hX old).mp hIncident
    · exfalso
      obtain ⟨-, hRel⟩ := (incident_branchVertex_iff setup _ _).mp hIncident
      rw [newSourceEdge_sheet setup y, branchPartition_rel_ordinary setup hX] at hRel
      have hFold := (newSourceEdge_survives_iff setup hValid y).mp hSurvives
      have hWallY : (data.vertexPartition wall).Rel anchor.1 y := by
        rcases hFold with rfl | rfl
        · exact setup.foldFirst_wall
        · exact setup.foldSecond_wall
      exact hX (hWallY.trans hRel.symm)
  · rintro ⟨old, hOld, rfl⟩
    obtain ⟨hSurv, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    exact ⟨ResolutionSurvival.not_isDangling_oldSourceEdge (cand) hValid.1 old hSurv,
      (incident_oldSourceEdge_branchVertex_ordinary setup hX old).mpr hInc⟩

/-- **`nd(B_v) = nd(B)`**: an ordinary block's surviving valency is unchanged. -/
theorem nonDanglingValency_branchVertex_ordinary (hValid : data.Valid) {x : Fin degree}
    (hX : ¬ (data.vertexPartition wall).Rel anchor.1 x) :
    nonDanglingValency (cand).datum (branchVertex setup x) =
      nonDanglingValency data (data.sourceEndpoint wall x) := by
  classical
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_branchVertex_ordinary setup hValid hX,
    Finset.card_image_of_injective _ (ResolutionCut.oldSourceEdge_injective (cand)),
    card_nonDanglingIncident]

/-! ## 10.  Non-vacuity of the census arithmetic

`BaseOneSetup` itself is inhabited through the partition model of
`NonTrivalentValencyTwoBaseOne` (`NonTrivalentValencyTwoBaseOne.modelPattern`
and the witnesses `baseOne_equal_witness`, `baseOne_semiEqual_witness`) and the
gauge model of `NonTrivalentValencyTwoGauge`
(`NonTrivalentValencyTwoGauge.gauge_model_exists`); the numbers the census
produces are recorded here on literal inputs. -/

section NonVacuity

/-- The Base I endpoint census on literal numbers: `nd(A) = 2 + 2 = 4` splits
into `nd(F) = 1 + 1 = 2` at the fold, `nd(A_i) = 1 + 1 + 1 = 3` at each vertex
above the new branch point, and `nd = 0` at every singleton above the leaf. -/
theorem baseOne_census_arithmetic :
    (4 : ℕ) = 2 + 2 ∧ (2 : ℕ) = 1 + 1 ∧ (3 : ℕ) = 1 + 1 + 1 ∧ (0 : ℕ) + 1 = 1 := by
  norm_num

/-- The blockwise Euler identity of the Base I resolution on a block of size
`k`: the new edge induces `k` occurrences, the leaf side `k - 1` classes (one
fold, `k - 2` singletons) and the branch side `2`. -/
theorem baseOne_euler_arithmetic (k : ℕ) (hk : 1 ≤ k) : k + 1 = (k - 1) + 2 := by
  omega

end NonVacuity

end DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRows
