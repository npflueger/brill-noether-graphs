module

public import DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor

@[expose] public section

/-!
# Part II valency-two anchor classifier

Source: Vargas, Part II, Section 5.4, case `{v2-nd4}`.  At a
divalent wall `w₀` the distinguished block `A` has `r₀(A) = 4 - val w₀ = 2`,
and `lem-rphi-nd` at surviving valency four then reads

```text
k₂ + k₃ + k₄ + k₅ = 2 |A|,
```

the identity already recorded datum-side as
`NonTrivalentWallSetup.sum_sourceEdgeIndex_eq_valency_two`.  Harmonicity bounds
the survivor-index sum in each literal target direction by `|A|`; with only two
directions available the two bounds must both be equalities, so

* both directions are active (`activeTargets_card_eq_two`), hence the active
  set is literally the whole divalent star (`activeTargets_eq_incidentEdges`);
* each direction carries survivor-index sum exactly `|A|`
  (`sum_directionSurvivors_eq`), which is the paper's `k₃ + k₄ = |A|` and
  `k₂ + k₅ = |A|` in Configuration A and its `|A| = k₅` and
  `|A| = k₂ + k₃ + k₄` in Configuration B (the opening computations of the two
  configurations);
* the four survivors split `2 + 2` (Configuration A, `{v2-nd4-t3}`)
  or `3 + 1` (Configuration B, `{v2-nd4-t2}`) (`twoBranchDistribution`).

In the `3 + 1` branch the lone survivor of the thin direction has index exactly
`|A|` (`sourceEdgeIndex_eq_blockCard_of_thin_direction`), which is the paper's
`|A| = k₅`; this is the datum the valency-two exit consumes to know that the
single class above `t₃` is the whole local degree.

## What is proved here, and what is not

Everything in this module is stated for an arbitrary `GluingDatum` and takes
as **explicit hypotheses**

* `hNoGlue : DanglingEdgeNoGlue data`,
* `hR : data.localRamification wall block = 2`,
* `hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4`,
* `star : W2R1Target.TwoStar target wall` (the divalent target star used by
  every existing divalent-wall module; no new star type is introduced).

Producing `hR` from an incoming one-row degeneration is the separate
`lemma-above-w0` rigidity step, carried out in
`NonTrivalentValencyTwoRigidity.localRamification_eq_two`; producing `hNd` is
the boundary dispatcher's obligation, exactly as in the valency-three pair.

The active-direction machinery of the valency-three classifier is **reused**,
not re-derived: `NonTrivalentValencyThreeAnchor.activeTargets`,
`mem_activeTargets`, `activeTargets_subset_incidentEdges` and
`sum_survivor_index_le_activeTargets` are star-free and are consumed verbatim.
Only the labelled `Fin 2` direction fibres are new.

No inhabitant of `TwoBranchAnchor` over a literal gluing datum is exhibited
here, for the same reason the valency-three `ThreeBranchAnchor` has none: that
would require a concrete `FullDimensionalSourcePresentation`, which is not
constructed here.  The
`NonVacuity` section below therefore discharges the *arithmetic* half on
literal inputs -- both index configurations of Part II §5.4 have solutions with
every `kᵢ` positive, and the survivor split of four into two nonempty
direction fibres is exactly the disjunction `TwoBranchDistribution` records --
so none of the new definitions is empty by arithmetic accident.

## Used by

`NonTrivalentValencyTwoRigidity` (which supplies `hR` and re-exports
`twoBranchAnchor` from the incoming contraction), and downstream the
prescribed-type valency-two exit.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource StableLocalProperties
open W3R1SourceProfile W2R1Target
open NonTrivalentValencyThreeAnchor (activeTargets mem_activeTargets
  activeTargets_subset_incidentEdges sum_survivor_index_le_activeTargets)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-! ## The index identity at a ramification-two block -/

/-- `lem-rphi-nd` read at a wall block, with the local ramification left
symbolic.  This is `W3R1SourceProfile.sum_survivor_index` without its
ramification-one specialization. -/
theorem sum_survivor_index_form {data : GluingDatum target degree}
    (hNoGlue : DanglingEdgeNoGlue data) (block : WallBlock data wall) :
    (∑ edge ∈ survivors data block, (data.sourceEdgeIndex edge.1 : ℤ)) =
      (nonDanglingValency data (WallBlock.sourceVertex data wall block) : ℤ) +
        2 * ((data.vertexPartition wall).blockCard block.1 : ℤ) - 2 -
          data.localRamification wall block := by
  have hForm := StableLocalProperties.localRamification_eq_nonDangling_form data hNoGlue
    (WallBlock.sourceVertex data wall block)
  have hRam : data.localRamification
      (WallBlock.sourceVertex data wall block).1.1
      ⟨(WallBlock.sourceVertex data wall block).1.2,
        (WallBlock.sourceVertex data wall block).2⟩ =
        data.localRamification wall block :=
    congrArg (data.localRamification wall) (Subtype.ext block.2)
  have hCard : (data.vertexPartition
      (WallBlock.sourceVertex data wall block).1.1).blockCard
        (WallBlock.sourceVertex data wall block).1.2 =
        (data.vertexPartition wall).blockCard block.1 :=
    congrArg (data.vertexPartition wall).blockCard block.2
  rw [hRam, hCard] at hForm
  change _ = _ - 2 + 2 * _ - ∑ edge ∈ survivors data block, _ at hForm
  linarith

/-- **Part II, Section 5.4: `lem-rphi-nd` at the anchor.**  At the
ramification-two anchor of surviving
valency four the four dilation indices sum to `2 |A|`. -/
theorem sum_survivor_index_eq_two_mul_blockCard {data : GluingDatum target degree}
    (hNoGlue : DanglingEdgeNoGlue data) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4) :
    (∑ edge ∈ survivors data block, (data.sourceEdgeIndex edge.1 : ℤ)) =
      2 * ((data.vertexPartition wall).blockCard block.1 : ℤ) := by
  rw [sum_survivor_index_form hNoGlue block, hR, hNd]
  push_cast
  ring

/-! ## Both directions of the divalent star are active -/

/-- Ramification two and four surviving occurrences force **both** target
directions at the divalent wall to occur: a single direction can absorb only
`|A|` units of index, against the required `2 |A|`. -/
theorem activeTargets_card_eq_two (data : GluingDatum target degree)
    (star : TwoStar target wall) (hNoGlue : DanglingEdgeNoGlue data)
    (block : WallBlock data wall)
    (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4) :
    (activeTargets data block).card = 2 := by
  have hUpper := Finset.card_le_card (activeTargets_subset_incidentEdges data block)
  rw [star.card_incidentEdges] at hUpper
  have hBound := sum_survivor_index_le_activeTargets data block
  rw [sum_survivor_index_eq_two_mul_blockCard hNoGlue block hR hNd] at hBound
  have hBlockPos := (data.vertexPartition wall).blockCard_pos block.1
  have hPos : (1 : ℤ) ≤ ((data.vertexPartition wall).blockCard block.1 : ℤ) := by
    exact_mod_cast hBlockPos
  by_contra hNe
  have hSmall : ((activeTargets data block).card : ℤ) ≤ 1 := by
    have : (activeTargets data block).card ≤ 1 := by omega
    exact_mod_cast this
  have hStep : ((activeTargets data block).card : ℤ) *
      ((data.vertexPartition wall).blockCard block.1 : ℤ) ≤
      1 * ((data.vertexPartition wall).blockCard block.1 : ℤ) :=
    mul_le_mul_of_nonneg_right hSmall (by linarith)
  linarith

/-- Hence the active target set is literally the whole divalent star. -/
theorem activeTargets_eq_incidentEdges (data : GluingDatum target degree)
    (star : TwoStar target wall) (hNoGlue : DanglingEdgeNoGlue data)
    (block : WallBlock data wall)
    (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4) :
    activeTargets data block = GluingDatum.incidentEdges wall := by
  apply Finset.eq_of_subset_of_card_le (activeTargets_subset_incidentEdges data block)
  rw [activeTargets_card_eq_two data star hNoGlue block hR hNd,
    star.card_incidentEdges]

/-! ## The two labelled direction fibres -/

/-- Label the literal target occurrence of an actual incident source flag. -/
noncomputable def survivorLabel (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) : Fin 2 :=
  star.label.symm ⟨edge.1.1.1, by
    have h := (incident_iff_target_mem_and_rel data edge.1
      (WallBlock.sourceVertex data wall block)).mp edge.2 |>.1
    simpa only [WallBlock.sourceVertex, GluingDatum.sourceEndpoint] using h⟩

theorem edge_survivorLabel (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    star.edge (survivorLabel data star block edge) = edge.1.1.1 :=
  congrArg Subtype.val (star.label.apply_symm_apply _)

/-- The surviving actual source occurrences in one named target direction. -/
noncomputable def directionSurvivors (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) (label : Fin 2) :
    Finset (IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :=
  (survivors data block).filter fun edge ↦ survivorLabel data star block edge = label

@[simp] theorem mem_directionSurvivors (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) (label : Fin 2)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    edge ∈ directionSurvivors data star block label ↔
      edge ∈ survivors data block ∧ edge.1.1.1 = star.edge label := by
  classical
  rw [directionSurvivors, Finset.mem_filter]
  constructor
  · rintro ⟨hSurvives, hLabel⟩
    exact ⟨hSurvives, (edge_survivorLabel data star block edge).symm.trans
      (congrArg star.edge hLabel)⟩
  · rintro ⟨hSurvives, hTarget⟩
    refine ⟨hSurvives, ?_⟩
    apply star.edge_injective
    rw [edge_survivorLabel]
    exact hTarget

/-- The two direction fibres partition all surviving actual incidences. -/
theorem sum_card_directionSurvivors (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) :
    ∑ label : Fin 2, (directionSurvivors data star block label).card =
      (survivors data block).card := by
  classical
  simp_rw [Finset.card_eq_sum_ones]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := survivors data block) (t := (Finset.univ : Finset (Fin 2)))
    (g := survivorLabel data star block) (fun _ _ ↦ Finset.mem_univ _)
    (fun _ ↦ 1)]
  rfl

/-- The two direction fibres also partition the survivor-index sum. -/
theorem sum_index_directionSurvivors (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) :
    (∑ label : Fin 2, ∑ edge ∈ directionSurvivors data star block label,
        (data.sourceEdgeIndex edge.1 : ℤ)) =
      ∑ edge ∈ survivors data block, (data.sourceEdgeIndex edge.1 : ℤ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := survivors data block) (t := (Finset.univ : Finset (Fin 2)))
    (g := survivorLabel data star block) (fun _ _ ↦ Finset.mem_univ _)
    (fun edge ↦ (data.sourceEdgeIndex edge.1 : ℤ))]
  rfl

/-- Harmonicity in one literal direction: the survivors above one target
occurrence carry at most the local degree. -/
theorem sum_index_directionSurvivors_le (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) (label : Fin 2) :
    (∑ edge ∈ directionSurvivors data star block label,
        (data.sourceEdgeIndex edge.1 : ℤ)) ≤
      ((data.vertexPartition wall).blockCard block.1 : ℤ) := by
  classical
  have hAt : star.edge label ∈
      GluingDatum.incidentEdges (WallBlock.sourceVertex data wall block).1.1 := by
    change star.edge label ∈ GluingDatum.incidentEdges wall
    exact star.edge_mem_incidentEdges label
  have hBound := W3R1SourceProfile.sum_index_le_of_same_target data
    (WallBlock.sourceVertex data wall block)
    (directionSurvivors data star block label) (star.edge label) hAt (by
      intro edge hEdge
      exact ((mem_directionSurvivors data star block label edge).mp hEdge).2)
  simpa only [WallBlock.sourceVertex, GluingDatum.sourceEndpoint, block.2] using hBound

/-- Each label is `0` or `1`. -/
theorem eq_zero_or_one (label : Fin 2) : label = 0 ∨ label = 1 := by
  rcases Nat.eq_zero_or_pos label.val with hZero | hPos
  · left
    apply Fin.ext
    exact hZero
  · right
    apply Fin.ext
    have hLt := label.isLt
    omega

/-- **Part II, Section 5.4, the opening computations of Configurations A and
B.**  Both direction sums are
*exactly* the local degree: they are each at most `|A|` and together `2 |A|`.
This is `k₃ + k₄ = |A|`, `k₂ + k₅ = |A|` in Configuration A and `|A| = k₅`,
`|A| = k₂ + k₃ + k₄` in Configuration B. -/
theorem sum_directionSurvivors_eq (data : GluingDatum target degree)
    (star : TwoStar target wall) (hNoGlue : DanglingEdgeNoGlue data)
    (block : WallBlock data wall)
    (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4)
    (label : Fin 2) :
    (∑ edge ∈ directionSurvivors data star block label,
        (data.sourceEdgeIndex edge.1 : ℤ)) =
      ((data.vertexPartition wall).blockCard block.1 : ℤ) := by
  have hTotal := (sum_index_directionSurvivors data star block).trans
    (sum_survivor_index_eq_two_mul_blockCard hNoGlue block hR hNd)
  rw [Fin.sum_univ_two] at hTotal
  have hZero := sum_index_directionSurvivors_le data star block 0
  have hOne := sum_index_directionSurvivors_le data star block 1
  rcases eq_zero_or_one label with rfl | rfl
  · linarith
  · linarith

/-- Both directions are nonempty, since both are active. -/
theorem card_directionSurvivors_pos (data : GluingDatum target degree)
    (star : TwoStar target wall) (hNoGlue : DanglingEdgeNoGlue data)
    (block : WallBlock data wall)
    (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4)
    (label : Fin 2) :
    0 < (directionSurvivors data star block label).card := by
  have hActive : star.edge label ∈ activeTargets data block := by
    rw [activeTargets_eq_incidentEdges data star hNoGlue block hR hNd]
    exact star.edge_mem_incidentEdges label
  obtain ⟨edge, hEdge, hTarget⟩ := (mem_activeTargets data block _).mp hActive
  exact Finset.card_pos.mpr ⟨edge,
    (mem_directionSurvivors data star block label edge).2 ⟨hEdge, hTarget⟩⟩

/-! ## The distribution -/

/-- **The exact source-facing valency-two survivor distribution.**
Configuration A of Part II §5.4 (`{v2-nd4-t3}`) puts two surviving
occurrences above each of the two target occurrences; Configuration B
(`{v2-nd4-t2}`) puts three above one and one above the other.
Counts are of literal source occurrences and labels name literal target
occurrences; there is no supplied active-label pattern. -/
def TwoBranchDistribution (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) : Prop :=
  (∀ label : Fin 2, (directionSurvivors data star block label).card = 2) ∨
    ∃ tripled : Fin 2,
      (directionSurvivors data star block tripled).card = 3 ∧
        ∀ label, label ≠ tripled →
          (directionSurvivors data star block label).card = 1

/-- The only splits of four survivors into two nonempty direction fibres are
`2 + 2`, `3 + 1` and `1 + 3`. -/
theorem card_split_of_four {first second : ℕ} (hFirst : 0 < first)
    (hSecond : 0 < second) (hSum : first + second = 4) :
    (first = 2 ∧ second = 2) ∨ (first = 3 ∧ second = 1) ∨
      (first = 1 ∧ second = 3) := by
  omega

/-- Four survivors at a ramification-two divalent wall split `2 + 2` or
`3 + 1` between the two literal target directions. -/
theorem twoBranchDistribution (data : GluingDatum target degree)
    (star : TwoStar target wall) (hNoGlue : DanglingEdgeNoGlue data)
    (block : WallBlock data wall)
    (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4) :
    TwoBranchDistribution data star block := by
  have hSum := sum_card_directionSurvivors data star block
  rw [card_survivors, hNd, Fin.sum_univ_two] at hSum
  have hZero := card_directionSurvivors_pos data star hNoGlue block hR hNd 0
  have hOne := card_directionSurvivors_pos data star hNoGlue block hR hNd 1
  rcases card_split_of_four hZero hOne hSum with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · refine Or.inl ?_
    intro label
    rcases eq_zero_or_one label with rfl | rfl
    · exact hA
    · exact hB
  · refine Or.inr ⟨0, hA, ?_⟩
    intro label hNe
    rcases eq_zero_or_one label with rfl | rfl
    · exact (hNe rfl).elim
    · exact hB
  · refine Or.inr ⟨1, hB, ?_⟩
    intro label hNe
    rcases eq_zero_or_one label with rfl | rfl
    · exact hA
    · exact (hNe rfl).elim

/-- **Part II, Section 5.4, Configuration B.**  A direction carrying a single
survivor carries it
with index exactly the local degree: `|A| = k₅`.  This is the fact
Configuration B's exit consumes. -/
theorem sourceEdgeIndex_eq_blockCard_of_thin_direction
    (data : GluingDatum target degree) (star : TwoStar target wall)
    (hNoGlue : DanglingEdgeNoGlue data) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4)
    (label : Fin 2) (hThin : (directionSurvivors data star block label).card = 1)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hEdge : edge ∈ directionSurvivors data star block label) :
    (data.sourceEdgeIndex edge.1 : ℤ) =
      ((data.vertexPartition wall).blockCard block.1 : ℤ) := by
  have hSingleton : directionSurvivors data star block label = {edge} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hEdge, fun other hOther ↦ ?_⟩
    exact Finset.card_le_one.mp (le_of_eq hThin) other hOther edge hEdge
  have hSum := sum_directionSurvivors_eq data star hNoGlue block hR hNd label
  rw [hSingleton, Finset.sum_singleton] at hSum
  exact hSum

/-! ## The classifier -/

/-- The modular source classifier for case `{v2-nd4}`.  Its sets and counts
refer to literal target occurrences and literal surviving source incidences. -/
structure TwoBranchAnchor (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) : Prop where
  active_all : activeTargets data block = GluingDatum.incidentEdges wall
  distribution : TwoBranchDistribution data star block
  direction_index_sum : ∀ label : Fin 2,
    (∑ edge ∈ directionSurvivors data star block label,
      (data.sourceEdgeIndex edge.1 : ℤ)) =
      ((data.vertexPartition wall).blockCard block.1 : ℤ)
  survivor_index_sum :
    (∑ edge ∈ survivors data block, (data.sourceEdgeIndex edge.1 : ℤ)) =
      2 * ((data.vertexPartition wall).blockCard block.1 : ℤ)

/-- Actual producer of the valency-two anchor from no-glue, ramification two,
and the distinguished block's surviving valency four. -/
theorem twoBranchAnchor (data : GluingDatum target degree)
    (star : TwoStar target wall) (hNoGlue : DanglingEdgeNoGlue data)
    (block : WallBlock data wall)
    (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 4) :
    TwoBranchAnchor data star block where
  active_all := activeTargets_eq_incidentEdges data star hNoGlue block hR hNd
  distribution := twoBranchDistribution data star hNoGlue block hR hNd
  direction_index_sum := sum_directionSurvivors_eq data star hNoGlue block hR hNd
  survivor_index_sum := sum_survivor_index_eq_two_mul_blockCard hNoGlue block hR hNd

/-! ## Non-vacuity of the classifier's arithmetic -/

section NonVacuity

/-- Configuration A of Part II §5.4 on literal inputs (all indices equal, as in
the subcase `{v2-nd4-t3-k2=k4}`): `|A| = 2`, `k = (1,1,1,1)`, both direction
sums `|A|`, total `2|A|`. -/
theorem configurationA_witness :
    (1 + 1 : ℤ) = 2 ∧ (1 + 1 : ℤ) = 2 ∧ (1 + 1 + 1 + 1 : ℤ) = 2 * 2 := by
  norm_num

/-- Configuration A on literal inputs with a strict index chain
(the subcase `{v2-nd4-t3-k2<k3}`, `k₂ < k₃ < k₄`): `|A| = 6`,
`k = (1, 2, 4, 5)`. -/
theorem configurationA_strict_witness :
    (2 + 4 : ℤ) = 6 ∧ (1 + 5 : ℤ) = 6 ∧ (1 + 2 + 4 + 5 : ℤ) = 2 * 6 ∧
      (1 : ℤ) < 2 ∧ (2 : ℤ) < 4 ∧ (4 : ℤ) < 5 := by
  norm_num

/-- Configuration B of Part II §5.4 on literal inputs: `|A| = 3`,
`k = (1,1,1,3)` with the thin direction's single index equal to `|A|`. -/
theorem configurationB_witness :
    (1 + 1 + 1 : ℤ) = 3 ∧ (3 : ℤ) = 3 ∧ (1 + 1 + 1 + 3 : ℤ) = 2 * 3 := by
  norm_num

/-- Both branches of `TwoBranchDistribution` are reachable and no other split
of four positive counts between two directions exists, so the disjunction is
neither empty nor missing a case. -/
theorem distribution_branches_exhaustive (first second : ℕ) (hFirst : 0 < first)
    (hSecond : 0 < second) (hSum : first + second = 4) :
    (first = 2 ∧ second = 2) ∨ (first = 3 ∧ second = 1) ∨
      (first = 1 ∧ second = 3) :=
  card_split_of_four hFirst hSecond hSum

end NonVacuity

end DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
