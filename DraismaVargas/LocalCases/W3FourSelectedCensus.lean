module

public import DraismaVargas.LocalCases.W3FourIncomingMatching
public import DraismaVargas.LocalCases.W3ShiftSelectedCensus

@[expose] public section

/-!
# The selected-block census at the `w3Four` wall

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Case
`{w3-r1-nd3-t2-(a=k₄)}`, with the Positions I / II.a / II.b of Case
`{w3-r1-nd3-t2}` and Figure 28.

This module determines the literal sheet classes an incoming `w3Four` cover
displays over the distinguished wall block `A₀` at the two
restored original endpoints and on the contracted occurrence.
`W3FourIncomingMatching` and `W3FourArbitraryExit` consume them as the
profile-free bundle `W3ShiftIncomingMatching.SelectedCensus`; here they are
**produced**, from `W3IncomingClassification.Classification.four`'s own payload
together with `fullDim`, `hForest` and `hCompat`.

## The route: block counts and one unit of ramification, not a fibre census

The Figure 29 census (`W3ShiftSelectedCensus`) goes through the pruned fibre:
an exact census of active constituents and internal
occurrences, then `W3Nd2IncomingSheetClasses`.  Figure 28 is settled by a
shorter route, and the reason is `k₄ = |A₀|`: the full-degree class already
fills `A₀`, so one endpoint's partition is *known* before any counting, and
what is left is arithmetic on `SheetPartition.blockCountWithin`.

The engine is three facts and nothing else.

* `ContractionRamification.localRamificationAt_contractDatum_merge` splits
  `r₀(A₀) = 1` (`ThirdEquation.W3SourceInput.localRamification_distinguishedBlock`)
  between the two original endpoints; the unramified one
  (`W3Nd2IncomingTargetPlacement.endpoint_valencies`) contributes nothing, so the
  whole unit sits above the **divalent** endpoint -- `ramification_sum_eq_one`.
* `ContractionRamification.contractionForest_count` is the tree identity
  `c + 1 = m + q` on induced block counts inside `A₀`.
* `ContractionRamification.block_eq_of_blockCountWithin_eq` upgrades an equality
  of induced counts to an equality of the classes themselves; it is what turns
  `c = q` into "the contracted occurrence and the trivalent endpoint carry the
  same classes", with no occurrence-by-occurrence matching anywhere.

The only place the pruned fibre is used at all is
`W3ShiftSelectedCensus.inactive_vertex_block` (consumed verbatim, profile-free)
together with `W3Nd3IncomingCensus.otherSide_card_le_one`: they say the divalent
original endpoint carries exactly one active class over `A₀` and that every other
class there is a literal singleton.  That is the whole `Orientation.activePoint`
field, and it is what excludes the arithmetically consistent but geometrically
impossible picture in which the ramification sits on a class disjoint from `e_α`.

## The three orientations, and what each produces

`Orientation` is the orientation-free packaging: `low` is the divalent original
endpoint, `high` the trivalent one, `alphaTarget` the wall direction restored at
`low` and `betaTarget`, `gammaTarget` the two restored at `high`.

* **`α = 4`** (`classes_of_largest_orientation`): `A₀` sits whole at the divalent
  endpoint (`low_block_eq_wall`), the contracted occurrence splits it in two
  (`contracted_count_eq_two`) and so does the trivalent endpoint
  (`high_count_eq_two`), and the two classes are either `e₂` and `e₃` -- Position
  I, and then `e₂ ∩ e₃ = ∅` is **produced**, not hypothesised -- or `A₀ ∖ {x}`
  and `{x}` for a single sheet `x` outside both -- Position II.b, and the
  `W3FourClosure.PositionTwo` datum is produced with the cover's own `x`.
* **`α = 2` or `α = 3`** (`classes_of_grow_orientation`): `A₀` sits whole at the
  *trivalent* endpoint, the divalent endpoint carries `e_α ∪ {y}` for exactly one
  further sheet `y` of `A₀` (`exists_extraSheet`, `low_alpha_blockCard`), and the
  contracted occurrence carries the same -- Position II.a, with the transferred
  sheet produced.

`exists_selectedCensus` is the trichotomy, on the classifier's payload alone.

## What is a hypothesis and what is not

Nothing beyond `W3IncomingClassification.Classification.four`'s payload (an
`Nd3Profile` of the distinguished block, three distinct target directions and
`k₄ = |A₀|`), the incoming full-dimensional presentation, the contraction forest
and dangling compatibility.  No `HasShrinkSheet`-style existence hypothesis, no
branch swap, no gauge copy: the identification lives over
`contractDatum data hc hab hOne` throughout, exactly as `W3FourIncomingCensus`
does.

**The one thing this file does not settle** is which of the `|A₀| − k_α` Position
II.a members on a given direction the cover is: `GrowProfile.growPartition` is
`mergeBlocks` at `GrowProfile.extraSheet`, an `Exists.choose`, so the census's
own sheet `y` has to be matched against it.  The match is automatic when
`|A₀| = k_α + 1`; in general it is made by carrying the transferred sheet as
data, `W3FourSourceCandidates.GrowProfile.withExtra` (as in
`W3FourIncomingMatching.figure28MembersWithExtra`), and Figure 29's
`W3ShiftSourceCandidates.ShiftProfile.withExtra` does the same.
-/

namespace DraismaVargas.LocalCases.W3FourSelectedCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open IncomingTargetExpansion IncomingW2TargetPlacement TargetExpansion
open PrunedFibreValency PrunedFibreTree FullContractionFibre
open W4IncomingRetainedFlags
open W3Nd2IncomingTargetPlacement (divalentOccurrence endpoint_valencies)
open W3FourSourceCandidates (GrowProfile growProfileFirst growProfileSecond)

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-! ## §1  Counting induced blocks -/

section Counting

variable {d : ℕ}

/-- `blockCountWithin` reads only the coarse block, so two coarse partitions
agreeing there give the same count. -/
theorem blockCountWithin_congr_coarse (fine first second : SheetPartition d) (i : Fin d)
    (hBlock : first.block i = second.block i) :
    fine.blockCountWithin first i = fine.blockCountWithin second i := by
  unfold SheetPartition.blockCountWithin
  rw [hBlock]

/-- A coarse block contains at most as many induced blocks as sheets. -/
theorem blockCountWithin_le_blockCard (fine coarse : SheetPartition d) (i : Fin d) :
    fine.blockCountWithin coarse i ≤ coarse.blockCard i := by
  unfold SheetPartition.blockCountWithin SheetPartition.blockCard
  exact Finset.card_image_le

/-- A refinement which is singleton-refined throughout one coarse block induces
exactly as many blocks there as the block has sheets. -/
theorem blockCountWithin_eq_blockCard_of_singletons (fine coarse : SheetPartition d)
    (hFine : fine.Refines coarse) (anchor : Fin d)
    (hAll : ∀ sheet, coarse.Rel anchor sheet → fine.blockCard sheet = 1) :
    fine.blockCountWithin coarse anchor = coarse.blockCard anchor := by
  have hCount := W3FourSourceCandidates.blockCountWithin_of_singletons_off_block fine coarse
    hFine anchor anchor rfl (fun sheet hSheet _ ↦ hAll sheet hSheet)
  have hOne : fine.blockCard anchor = 1 := hAll anchor rfl
  omega

/-- A refinement whose class through a sheet already fills the coarse block
induces exactly one block there. -/
theorem blockCountWithin_eq_one_of_block_eq (fine coarse : SheetPartition d) (i : Fin d)
    (hEq : fine.block i = coarse.block i) : fine.blockCountWithin coarse i = 1 := by
  classical
  have hImage : (coarse.block i).image fine.repr = {fine.repr i} := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro value hValue
      obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hValue
      refine Finset.mem_singleton.mpr ?_
      have hRel : fine.Rel i source := (fine.mem_block_iff i source).mp (hEq ▸ hSource)
      exact hRel.symm
    · intro value hValue
      rw [Finset.mem_singleton.mp hValue]
      exact Finset.mem_image.mpr ⟨i, coarse.self_mem_block i, rfl⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_singleton]

/-- Disjoint blocks are unrelated. -/
theorem not_rel_of_disjoint {first second : SheetPartition d} {i j : Fin d}
    (hDisjoint : Disjoint (first.block i) (second.block j)) : ¬first.Rel i j := fun hRel ↦
  Finset.disjoint_left.mp hDisjoint ((first.mem_block_iff _ _).mpr hRel)
    (second.self_mem_block j)

end Counting

/-! ## §2  Reading a local ramification off an exact star -/

section Ramification

variable (data : GluingDatum target degree)

/-- The local ramification at a **divalent** target vertex whose star is the
named pair. -/
theorem localRamification_of_pair (vertex : target.V) (first second : target.edges)
    (hNe : first ≠ second)
    (hStar : GluingDatum.incidentEdges vertex = {first, second})
    (block : (data.vertexPartition vertex).Blocks) :
    data.localRamification vertex block =
      ((data.edgePartition first).blockCountWithin
          (data.vertexPartition vertex) block.1 : ℤ) +
        ((data.edgePartition second).blockCountWithin
          (data.vertexPartition vertex) block.1 : ℤ) - 2 := by
  classical
  unfold GluingDatum.localRamification
  rw [hStar, Finset.sum_pair hNe, Finset.card_pair hNe]
  ring

/-- The local ramification at a **trivalent** target vertex whose star is the
named triple. -/
theorem localRamification_of_triple (vertex : target.V)
    (first second third : target.edges)
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third)
    (hSecondThird : second ≠ third)
    (hStar : GluingDatum.incidentEdges vertex = {first, second, third})
    (block : (data.vertexPartition vertex).Blocks) :
    data.localRamification vertex block =
      ((data.edgePartition first).blockCountWithin
          (data.vertexPartition vertex) block.1 : ℤ) +
        ((data.edgePartition second).blockCountWithin
          (data.vertexPartition vertex) block.1 : ℤ) +
        ((data.edgePartition third).blockCountWithin
          (data.vertexPartition vertex) block.1 : ℤ) - 2 -
        ((data.vertexPartition vertex).blockCard block.1 : ℤ) := by
  classical
  unfold GluingDatum.localRamification
  have hSum : (∑ edge ∈ ({first, second, third} : Finset target.edges),
      ((data.edgePartition edge).blockCountWithin
        (data.vertexPartition vertex) block.1 : ℤ)) =
      ((data.edgePartition first).blockCountWithin
          (data.vertexPartition vertex) block.1 : ℤ) +
        ((data.edgePartition second).blockCountWithin
          (data.vertexPartition vertex) block.1 : ℤ) +
        ((data.edgePartition third).blockCountWithin
          (data.vertexPartition vertex) block.1 : ℤ) := by
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hFirstSecond, hFirstThird⟩),
      Finset.sum_pair hSecondThird]
    ring
  have hCard : ({first, second, third} : Finset target.edges).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hFirstSecond, hFirstThird⟩),
      Finset.card_pair hSecondThird]
  rw [hStar, hSum, hCard]
  ring

/-- Every local ramification of a valid datum is nonnegative. -/
theorem localRamification_nonneg_of_valid (hValid : data.Valid) (vertex : target.V)
    (block : (data.vertexPartition vertex).Blocks) :
    0 ≤ data.localRamification vertex block :=
  GluingDatum.localRamification_nonneg data vertex (fun sheet ↦ hValid.2 vertex sheet) block

/-- At an unramified target vertex every local ramification vanishes. -/
theorem localRamification_eq_zero_of_targetChange (hValid : data.Valid)
    (vertex : target.V) (hChange : data.targetChange vertex = 0)
    (block : (data.vertexPartition vertex).Blocks) :
    data.localRamification vertex block = 0 := by
  classical
  have hNonneg : ∀ other : (data.vertexPartition vertex).Blocks,
      0 ≤ data.localRamification vertex other :=
    fun other ↦ localRamification_nonneg_of_valid data hValid vertex other
  have hSum : (∑ other : (data.vertexPartition vertex).Blocks,
      data.localRamification vertex other) = 0 := hChange
  exact le_antisymm
    (Finset.single_le_sum (f := fun other : (data.vertexPartition vertex).Blocks ↦
        data.localRamification vertex other)
      (fun other _ ↦ hNonneg other) (Finset.mem_univ block) |>.trans_eq hSum)
    (hNonneg block)

end Ramification

/-! ## §3  The incoming picture at a `w3Four` wall -/

section Picture

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

/-- The distinguished wall block, as a block of the merged partition.  This is
`W3Nd2IncomingSelectedCensus.selectedBlock`, reused so that the pruned-fibre
lemmas apply on the nose. -/
noncomputable def wallBlock : (mergedPartition data a b).Blocks :=
  W3Nd2IncomingSelectedCensus.selectedBlock data hc hab hOne star input

@[simp] theorem wallBlock_val :
    (wallBlock data hc hab hOne input).1 = input.distinguishedBlock.1 := rfl

/-- Every block of the contracted wall partition met by `A₀` is `A₀`. -/
theorem wall_block_eq_root (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet =
      (mergedPartition data a b).block input.distinguishedBlock.1 := by
  rw [← W3ShiftIncomingMatching.merged_block_eq_wall_block data hc hab hOne]
  exact ((mergedPartition data a b).block_eq_of_rel hSheet).symm

end Picture

/-- **The incoming picture at a `w3Four` wall, in orientation-free form.**

`low` is the divalent original endpoint of the contracted occurrence and `high`
the trivalent one; `alphaTarget` is the wall direction restored at `low` and
`betaTarget`, `gammaTarget` the two restored at `high`.  The anchors are the
three survivors' own sheet representatives, the singleton fields are the wall
datum's own `blockCard_eq_one_of_not_rel` census off each survivor's class, and
`activePoint` is the fibre's unique active constituent above `low`. -/
structure Orientation {target : CFGraph} {degree : ℕ} {a b : target.V}
    {contracted : target.edges} (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W3SourceInput (contractDatum data hc hab hOne) star) where
  /-- The divalent original endpoint. -/
  low : target.V
  /-- The trivalent original endpoint. -/
  high : target.V
  low_mem : low = a ∨ low = b
  high_mem : high = a ∨ high = b
  low_ne_high : low ≠ high
  low_card : (GluingDatum.incidentEdges low).card = 2
  high_card : (GluingDatum.incidentEdges high).card = 3
  low_change : data.targetChange low = 1
  high_change : data.targetChange high = 0
  /-- `t_α`, restored at the divalent endpoint. -/
  alphaTarget : (contract target hab hOne).edges
  /-- `t_β`, restored at the trivalent endpoint. -/
  betaTarget : (contract target hab hOne).edges
  /-- `t_γ`, restored at the trivalent endpoint. -/
  gammaTarget : (contract target hab hOne).edges
  alpha_ne_beta : alphaTarget ≠ betaTarget
  alpha_ne_gamma : alphaTarget ≠ gammaTarget
  beta_ne_gamma : betaTarget ≠ gammaTarget
  alpha_at_low : unfoldEdge hc hab hOne alphaTarget ∈ GluingDatum.incidentEdges low
  beta_at_high : unfoldEdge hc hab hOne betaTarget ∈ GluingDatum.incidentEdges high
  gamma_at_high : unfoldEdge hc hab hOne gammaTarget ∈ GluingDatum.incidentEdges high
  /-- A sheet of `e_α`. -/
  alphaAnchor : Fin degree
  /-- A sheet of `e_β`. -/
  betaAnchor : Fin degree
  /-- A sheet of `e_γ`. -/
  gammaAnchor : Fin degree
  alpha_rel : (mergedPartition data a b).Rel input.distinguishedBlock.1 alphaAnchor
  beta_rel : (mergedPartition data a b).Rel input.distinguishedBlock.1 betaAnchor
  gamma_rel : (mergedPartition data a b).Rel input.distinguishedBlock.1 gammaAnchor
  alpha_singletons : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
    ¬(data.edgePartition (unfoldEdge hc hab hOne alphaTarget)).Rel alphaAnchor sheet →
    (data.edgePartition (unfoldEdge hc hab hOne alphaTarget)).blockCard sheet = 1
  beta_singletons : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
    ¬(data.edgePartition (unfoldEdge hc hab hOne betaTarget)).Rel betaAnchor sheet →
    (data.edgePartition (unfoldEdge hc hab hOne betaTarget)).blockCard sheet = 1
  gamma_singletons : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
    ¬(data.edgePartition (unfoldEdge hc hab hOne gammaTarget)).Rel gammaAnchor sheet →
    (data.edgePartition (unfoldEdge hc hab hOne gammaTarget)).blockCard sheet = 1
  index_sum :
    (data.edgePartition (unfoldEdge hc hab hOne alphaTarget)).blockCard alphaAnchor +
      (data.edgePartition (unfoldEdge hc hab hOne betaTarget)).blockCard betaAnchor +
      (data.edgePartition (unfoldEdge hc hab hOne gammaTarget)).blockCard gammaAnchor =
    2 * (mergedPartition data a b).blockCard input.distinguishedBlock.1
  /-- The fibre's unique active constituent above the divalent endpoint. -/
  activePoint : data.SourceVertex
  active_filter : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne (wallBlock data hc hab hOne input))).filter
      (fun point ↦ point.1.1 = low) = {activePoint}
  active_target : activePoint.1.1 = low
  active_rel : (data.vertexPartition low).Rel activePoint.1.2 alphaAnchor

/-! ## §4  The picture's derived star, refinements and singletons -/

theorem unfoldEdge_injective (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Function.Injective (unfoldEdge hc hab hOne) := fun _ _ hEq ↦
  (foldEdgeEquiv hc hab hOne).symm.injective (Subtype.ext hEq)

namespace Orientation

variable {data : GluingDatum target degree}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1}
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  {input : W3SourceInput (contractDatum data hc hab hOne) star}
  (o : Orientation data hc hab hOne input)

/-- `e_α`'s original target occurrence. -/
noncomputable abbrev alphaEdge : target.edges := unfoldEdge hc hab hOne o.alphaTarget

/-- `e_β`'s original target occurrence. -/
noncomputable abbrev betaEdge : target.edges := unfoldEdge hc hab hOne o.betaTarget

/-- `e_γ`'s original target occurrence. -/
noncomputable abbrev gammaEdge : target.edges := unfoldEdge hc hab hOne o.gammaTarget

/-- `index_sum`, restated on the unfolded occurrences. -/
theorem index_sum' :
    (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor +
        (data.edgePartition o.betaEdge).blockCard o.betaAnchor +
        (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      2 * (mergedPartition data a b).blockCard input.distinguishedBlock.1 := o.index_sum

/-- `alpha_singletons`, restated on the unfolded occurrence. -/
theorem alpha_singletons' (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬(data.edgePartition o.alphaEdge).Rel o.alphaAnchor sheet) :
    (data.edgePartition o.alphaEdge).blockCard sheet = 1 :=
  o.alpha_singletons sheet hSheet hNe

/-- `beta_singletons`, restated on the unfolded occurrence. -/
theorem beta_singletons' (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬(data.edgePartition o.betaEdge).Rel o.betaAnchor sheet) :
    (data.edgePartition o.betaEdge).blockCard sheet = 1 :=
  o.beta_singletons sheet hSheet hNe

/-- `gamma_singletons`, restated on the unfolded occurrence. -/
theorem gamma_singletons' (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬(data.edgePartition o.gammaEdge).Rel o.gammaAnchor sheet) :
    (data.edgePartition o.gammaEdge).blockCard sheet = 1 :=
  o.gamma_singletons sheet hSheet hNe

theorem contracted_mem_low : contracted ∈ GluingDatum.incidentEdges o.low := by
  rcases o.low_mem with h | h
  · rw [h]; exact contracted_mem_incidentEdges_left hc
  · rw [h]; exact contracted_mem_incidentEdges_right hc

theorem contracted_mem_high : contracted ∈ GluingDatum.incidentEdges o.high := by
  rcases o.high_mem with h | h
  · rw [h]; exact contracted_mem_incidentEdges_left hc
  · rw [h]; exact contracted_mem_incidentEdges_right hc

theorem low_star : GluingDatum.incidentEdges o.low = {contracted, o.alphaEdge} := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact o.contracted_mem_low
    · rw [Finset.mem_singleton.mp hEdge]; exact o.alpha_at_low
  · rw [o.low_card, Finset.card_pair (Ne.symm (unfoldEdge_ne_contracted hc hab hOne _))]

theorem high_star :
    GluingDatum.incidentEdges o.high = {contracted, o.betaEdge, o.gammaEdge} := by
  classical
  have hBetaGamma : o.betaEdge ≠ o.gammaEdge := fun hEq ↦
    o.beta_ne_gamma (unfoldEdge_injective hc hab hOne hEq)
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl | rfl
    · exact o.contracted_mem_high
    · exact o.beta_at_high
    · exact o.gamma_at_high
  · rw [o.high_card, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm (unfoldEdge_ne_contracted hc hab hOne _),
        Ne.symm (unfoldEdge_ne_contracted hc hab hOne _)⟩),
      Finset.card_pair hBetaGamma]

theorem beta_ne_gamma_edge : o.betaEdge ≠ o.gammaEdge := fun hEq ↦
  o.beta_ne_gamma (unfoldEdge_injective hc hab hOne hEq)

theorem refines_low : (data.vertexPartition o.low).Refines (mergedPartition data a b) := by
  rcases o.low_mem with h | h
  · rw [h]; exact vertexPartition_refines_mergedPartition data a b
  · rw [h]; exact vertexPartition_refines_mergedPartition_right data a b

theorem refines_high : (data.vertexPartition o.high).Refines (mergedPartition data a b) := by
  rcases o.high_mem with h | h
  · rw [h]; exact vertexPartition_refines_mergedPartition data a b
  · rw [h]; exact vertexPartition_refines_mergedPartition_right data a b

theorem contracted_refines_low :
    (data.edgePartition contracted).Refines (data.vertexPartition o.low) :=
  refines_of_mem_incidentEdges data o.contracted_mem_low

theorem contracted_refines_high :
    (data.edgePartition contracted).Refines (data.vertexPartition o.high) :=
  refines_of_mem_incidentEdges data o.contracted_mem_high

theorem alpha_refines_low :
    (data.edgePartition o.alphaEdge).Refines (data.vertexPartition o.low) :=
  refines_of_mem_incidentEdges data o.alpha_at_low

theorem beta_refines_high :
    (data.edgePartition o.betaEdge).Refines (data.vertexPartition o.high) :=
  refines_of_mem_incidentEdges data o.beta_at_high

theorem gamma_refines_high :
    (data.edgePartition o.gammaEdge).Refines (data.vertexPartition o.high) :=
  refines_of_mem_incidentEdges data o.gamma_at_high

/-- Every survivor's class sits inside the distinguished wall block. -/
theorem alpha_block_subset : (data.edgePartition o.alphaEdge).block o.alphaAnchor ⊆
    (mergedPartition data a b).block input.distinguishedBlock.1 := by
  intro sheet hSheet
  refine ((mergedPartition data a b).mem_block_iff _ _).mpr (o.alpha_rel.trans ?_)
  exact o.refines_low.rel (o.alpha_refines_low.rel
    (((data.edgePartition o.alphaEdge).mem_block_iff _ _).mp hSheet))

theorem beta_block_subset : (data.edgePartition o.betaEdge).block o.betaAnchor ⊆
    (mergedPartition data a b).block input.distinguishedBlock.1 := by
  intro sheet hSheet
  refine ((mergedPartition data a b).mem_block_iff _ _).mpr (o.beta_rel.trans ?_)
  exact o.refines_high.rel (o.beta_refines_high.rel
    (((data.edgePartition o.betaEdge).mem_block_iff _ _).mp hSheet))

theorem gamma_block_subset : (data.edgePartition o.gammaEdge).block o.gammaAnchor ⊆
    (mergedPartition data a b).block input.distinguishedBlock.1 := by
  intro sheet hSheet
  refine ((mergedPartition data a b).mem_block_iff _ _).mpr (o.gamma_rel.trans ?_)
  exact o.refines_high.rel (o.gamma_refines_high.rel
    (((data.edgePartition o.gammaEdge).mem_block_iff _ _).mp hSheet))

end Orientation

/-! ## §5  Splitting the wall's ramification between the two original endpoints -/

section Split

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

/-- Above an unramified original endpoint every merged-block summand vanishes. -/
theorem ramification_sum_eq_zero (hValid : data.Valid) (place : target.V)
    (hChange : data.targetChange place = 0) :
    (∑ block ∈ SheetPartition.blocksWithin (data.vertexPartition place)
        (mergedPartition data a b) (wallBlock data hc hab hOne input),
      data.localRamification place block) = 0 :=
  Finset.sum_eq_zero fun block _ ↦
    localRamification_eq_zero_of_targetChange data hValid place hChange block

/-- **The wall's unit of ramification sits above the divalent endpoint.**
`prop-rphi-under-contraction` splits `r₀(A₀) = 1` between the two original
endpoints, and the unramified one contributes nothing. -/
theorem ramification_sum_eq_one (hForest : ContractionForest data a b contracted)
    (hValid : data.Valid) (place other : target.V)
    (hPlace : place = a ∨ place = b) (hOther : other = a ∨ other = b)
    (hNe : place ≠ other) (hChange : data.targetChange other = 0) :
    (∑ block ∈ SheetPartition.blocksWithin (data.vertexPartition place)
        (mergedPartition data a b) (wallBlock data hc hab hOne input),
      data.localRamification place block) = 1 := by
  have hMerge := localRamificationAt_contractDatum_merge data hc hab hOne hForest
    (wallBlock data hc hab hOne input)
  have hWall : localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩
      (wallBlock data hc hab hOne input).1 = 1 :=
    input.localRamification_distinguishedBlock
  rw [hWall] at hMerge
  rcases hPlace with rfl | rfl
  · rcases hOther with rfl | rfl
    · exact absurd rfl hNe
    · have hZero := ramification_sum_eq_zero data hc hab hOne input hValid other hChange
      omega
  · rcases hOther with rfl | rfl
    · have hZero := ramification_sum_eq_zero data hc hab hOne input hValid other hChange
      omega
    · exact absurd rfl hNe

end Split

/-! ## §6  The divalent endpoint: singletons off the active class -/

namespace Orientation

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1}
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  {input : W3SourceInput (contractDatum data hc hab hOne) star}
  (o : Orientation data hc hab hOne input)

/-- **Every class above the divalent original endpoint other than the active
one is a literal singleton.**  `W3ShiftSelectedCensus.inactive_vertex_block` is
consumed verbatim: it mentions no profile and no figure, only the fibre's
active filter above one original endpoint. -/
theorem low_block_singleton (fullDim : FullDimensionalSourcePresentation data coordinate)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet)
    (hNot : ¬(data.vertexPartition o.low).Rel o.alphaAnchor sheet) :
    (data.vertexPartition o.low).block sheet = {sheet} := by
  refine W3ShiftSelectedCensus.inactive_vertex_block data hc hab hOne fullDim
    (wallBlock data hc hab hOne input) o.low o.low_mem o.activePoint o.active_filter
    sheet (((mergedPartition data a b).mem_block_iff _ _).mpr hSheet) ?_
  intro hMem
  exact hNot (o.active_rel.symm.trans
    (((data.vertexPartition o.low).mem_block_iff _ _).mp hMem))

theorem low_blockCard_singleton
    (fullDim : FullDimensionalSourcePresentation data coordinate) (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet)
    (hNot : ¬(data.vertexPartition o.low).Rel o.alphaAnchor sheet) :
    (data.vertexPartition o.low).blockCard sheet = 1 := by
  unfold SheetPartition.blockCard
  rw [o.low_block_singleton fullDim sheet hSheet hNot]
  simp

/-- The induced block count above the divalent endpoint: one class of size
`|A'|` and `|A₀| − |A'|` singletons. -/
theorem low_blockCount (fullDim : FullDimensionalSourcePresentation data coordinate) :
    (data.vertexPartition o.low).blockCountWithin (mergedPartition data a b)
        input.distinguishedBlock.1 +
      (data.vertexPartition o.low).blockCard o.alphaAnchor =
    (mergedPartition data a b).blockCard input.distinguishedBlock.1 + 1 :=
  W3FourSourceCandidates.blockCountWithin_of_singletons_off_block _ _ o.refines_low
    input.distinguishedBlock.1 o.alphaAnchor o.alpha_rel
    (fun sheet hSheet hNe ↦ o.low_blockCard_singleton fullDim sheet hSheet hNe)

/-- A singleton class above the divalent endpoint is unramified. -/
theorem low_ramification_of_singleton (block : (data.vertexPartition o.low).Blocks)
    (hCard : (data.vertexPartition o.low).blockCard block.1 = 1) :
    data.localRamification o.low block = 0 := by
  rw [localRamification_of_pair data o.low contracted o.alphaEdge
    (Ne.symm (unfoldEdge_ne_contracted hc hab hOne _)) o.low_star block]
  have h1 := SheetPartition.blockCountWithin_pos (data.edgePartition contracted)
    (data.vertexPartition o.low) block.1
  have h2 := blockCountWithin_le_blockCard (data.edgePartition contracted)
    (data.vertexPartition o.low) block.1
  have h3 := SheetPartition.blockCountWithin_pos (data.edgePartition o.alphaEdge)
    (data.vertexPartition o.low) block.1
  have h4 := blockCountWithin_le_blockCard (data.edgePartition o.alphaEdge)
    (data.vertexPartition o.low) block.1
  rw [hCard] at h2 h4
  omega

theorem alphaBlock_mem_blocksWithin :
    (data.vertexPartition o.low).toBlock o.alphaAnchor ∈
      SheetPartition.blocksWithin (data.vertexPartition o.low) (mergedPartition data a b)
        (wallBlock data hc hab hOne input) := by
  rw [SheetPartition.mem_blocksWithin]
  refine (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel _ _ _ _).mpr ?_
  exact o.alpha_rel.trans (o.refines_low.rel
    ((data.vertexPartition o.low).rel_repr_right o.alphaAnchor))

/-- **The wall's unit of ramification sits on the class carrying `e_α`.** -/
theorem low_ramification_eq_one (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted) :
    data.localRamification o.low
      ((data.vertexPartition o.low).toBlock o.alphaAnchor) = 1 := by
  classical
  have hSum := ramification_sum_eq_one data hc hab hOne input hForest fullDim.valid
    o.low o.high o.low_mem o.high_mem o.low_ne_high o.high_change
  rw [Finset.sum_eq_single_of_mem ((data.vertexPartition o.low).toBlock o.alphaAnchor)
    o.alphaBlock_mem_blocksWithin ?_] at hSum
  · exact hSum
  · intro block hBlock hNe
    refine o.low_ramification_of_singleton block (o.low_blockCard_singleton fullDim block.1 ?_ ?_)
    · exact (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel _ _ _ _).mp
        ((SheetPartition.mem_blocksWithin _ _ _ _).mp hBlock)
    · intro hRel
      refine hNe (Subtype.ext ?_)
      change block.1 = (data.vertexPartition o.low).repr o.alphaAnchor
      rw [hRel, block.2]

end Orientation

/-! ## §7  The `α = 4` orientation: `A₀` sits whole at the divalent endpoint -/

namespace Orientation

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1}
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  {input : W3SourceInput (contractDatum data hc hab hOne) star}
  (o : Orientation data hc hab hOne input)

/-- With `k_α = |A₀|` the restored class at the divalent endpoint fills the
whole distinguished wall block. -/
theorem alpha_block_eq_wall
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.edgePartition o.alphaEdge).block o.alphaAnchor =
      (mergedPartition data a b).block input.distinguishedBlock.1 :=
  Finset.eq_of_subset_of_card_le o.alpha_block_subset (le_of_eq hAlphaIndex.symm)

theorem alpha_rel_of_wall
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.vertexPartition o.low).Rel o.alphaAnchor sheet := by
  refine o.alpha_refines_low.rel
    (((data.edgePartition o.alphaEdge).mem_block_iff _ _).mp ?_)
  rw [o.alpha_block_eq_wall hAlphaIndex]
  exact ((mergedPartition data a b).mem_block_iff _ _).mpr hSheet

/-- **Position I / II.b, left class.**  The divalent original endpoint carries
the whole merged wall block. -/
theorem low_block_eq_wall
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.vertexPartition o.low).block sheet = (mergedPartition data a b).block sheet := by
  refine Finset.Subset.antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · exact ((mergedPartition data a b).mem_block_iff _ _).mpr
      (o.refines_low.rel (((data.vertexPartition o.low).mem_block_iff _ _).mp ht))
  · refine ((data.vertexPartition o.low).mem_block_iff _ _).mpr ?_
    have hFirst := o.alpha_rel_of_wall hAlphaIndex sheet hSheet
    have hSecond := o.alpha_rel_of_wall hAlphaIndex t
      (hSheet.trans (((mergedPartition data a b).mem_block_iff _ _).mp ht))
    exact hFirst.symm.trans hSecond

theorem low_blockCount_eq_one
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.vertexPartition o.low).blockCountWithin (mergedPartition data a b)
      input.distinguishedBlock.1 = 1 :=
  blockCountWithin_eq_one_of_block_eq _ _ _ (o.low_block_eq_wall hAlphaIndex _ rfl)

theorem alpha_blockCount_eq_one
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.edgePartition o.alphaEdge).blockCountWithin (data.vertexPartition o.low)
      o.alphaAnchor = 1 := by
  refine blockCountWithin_eq_one_of_block_eq _ _ _ ?_
  rw [o.alpha_block_eq_wall hAlphaIndex,
    o.low_block_eq_wall hAlphaIndex o.alphaAnchor o.alpha_rel,
    (mergedPartition data a b).block_eq_of_rel o.alpha_rel]

/-- **Two new occurrences.**  The wall's unit of ramification, read at the
divalent endpoint whose star is `{contracted, t_α}` and whose only class is
`A₀` itself, says the contracted occurrence splits `A₀` in two. -/
theorem contracted_count_eq_two
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.edgePartition contracted).blockCountWithin (mergedPartition data a b)
      input.distinguishedBlock.1 = 2 := by
  have hRam := o.low_ramification_eq_one fullDim hForest
  rw [localRamification_of_pair data o.low contracted o.alphaEdge
    (Ne.symm (unfoldEdge_ne_contracted hc hab hOne _)) o.low_star _] at hRam
  have hReprContracted : (data.edgePartition contracted).blockCountWithin
      (data.vertexPartition o.low)
      ((data.vertexPartition o.low).toBlock o.alphaAnchor).1 =
      (data.edgePartition contracted).blockCountWithin (data.vertexPartition o.low)
        o.alphaAnchor :=
    ContractionRamification.blockCountWithin_congr _ _
      ((data.vertexPartition o.low).rel_repr_left o.alphaAnchor)
  have hReprAlpha : (data.edgePartition o.alphaEdge).blockCountWithin
      (data.vertexPartition o.low)
      ((data.vertexPartition o.low).toBlock o.alphaAnchor).1 =
      (data.edgePartition o.alphaEdge).blockCountWithin (data.vertexPartition o.low)
        o.alphaAnchor :=
    ContractionRamification.blockCountWithin_congr _ _
      ((data.vertexPartition o.low).rel_repr_left o.alphaAnchor)
  have hCoarse : (data.edgePartition contracted).blockCountWithin
      (data.vertexPartition o.low) o.alphaAnchor =
      (data.edgePartition contracted).blockCountWithin (mergedPartition data a b)
        o.alphaAnchor :=
    blockCountWithin_congr_coarse _ _ _ _
      (o.low_block_eq_wall hAlphaIndex o.alphaAnchor o.alpha_rel)
  have hRoot : (data.edgePartition contracted).blockCountWithin
      (mergedPartition data a b) input.distinguishedBlock.1 =
      (data.edgePartition contracted).blockCountWithin (mergedPartition data a b)
        o.alphaAnchor :=
    ContractionRamification.blockCountWithin_congr _ _ o.alpha_rel
  rw [hReprContracted, hReprAlpha, hCoarse, o.alpha_blockCount_eq_one hAlphaIndex] at hRam
  omega

/-- The trivalent original endpoint therefore carries exactly two classes over
`A₀` as well: this is `ContractionForest` at the distinguished block. -/
theorem high_count_eq_two
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.vertexPartition o.high).blockCountWithin (mergedPartition data a b)
      input.distinguishedBlock.1 = 2 := by
  have hForestCount := contractionForest_count data hc hForest
    (wallBlock data hc hab hOne input)
  simp only [wallBlock_val] at hForestCount
  have hLowOne := o.low_blockCount_eq_one hAlphaIndex
  have hTwo := o.contracted_count_eq_two fullDim hForest hAlphaIndex
  rcases o.low_mem with hL | hL <;> rcases o.high_mem with hH | hH
  · exact absurd (hL.trans hH.symm) o.low_ne_high
  · rw [hL] at hLowOne; rw [hH]; omega
  · rw [hL] at hLowOne; rw [hH]; omega
  · exact absurd (hL.trans hH.symm) o.low_ne_high

/-- **The new occurrence and the trivalent endpoint carry the same classes.**
Both induce two blocks inside `A₀` and one refines the other. -/
theorem contracted_block_eq_high
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition contracted).block sheet =
      (data.vertexPartition o.high).block sheet :=
  block_eq_of_blockCountWithin_eq (data.edgePartition contracted)
    (data.vertexPartition o.high) (mergedPartition data a b) o.contracted_refines_high
    o.refines_high (wallBlock data hc hab hOne input)
    (by
      simp only [wallBlock_val]
      rw [o.contracted_count_eq_two fullDim hForest hAlphaIndex,
        o.high_count_eq_two fullDim hForest hAlphaIndex])
    sheet hSheet

end Orientation

/-! ## §8  The `α = 4` dichotomy at the trivalent endpoint -/

namespace Orientation

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1}
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  {input : W3SourceInput (contractDatum data hc hab hOne) star}
  (o : Orientation data hc hab hOne input)

/-- `k_β + k_γ = |A₀|` when `k_α = |A₀|`. -/
theorem beta_gamma_index_sum
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.edgePartition o.betaEdge).blockCard o.betaAnchor +
        (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1 := by
  have hSum := o.index_sum'
  omega

theorem high_block_subset (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.vertexPartition o.high).block sheet ⊆
      (mergedPartition data a b).block input.distinguishedBlock.1 := by
  intro t ht
  exact ((mergedPartition data a b).mem_block_iff _ _).mpr
    (hSheet.trans (o.refines_high.rel
      (((data.vertexPartition o.high).mem_block_iff _ _).mp ht)))

theorem beta_subset_high_block :
    (data.edgePartition o.betaEdge).block o.betaAnchor ⊆
      (data.vertexPartition o.high).block o.betaAnchor := by
  intro t ht
  exact ((data.vertexPartition o.high).mem_block_iff _ _).mpr
    (o.beta_refines_high.rel (((data.edgePartition o.betaEdge).mem_block_iff _ _).mp ht))

theorem gamma_subset_high_block :
    (data.edgePartition o.gammaEdge).block o.gammaAnchor ⊆
      (data.vertexPartition o.high).block o.gammaAnchor := by
  intro t ht
  exact ((data.vertexPartition o.high).mem_block_iff _ _).mpr
    (o.gamma_refines_high.rel (((data.edgePartition o.gammaEdge).mem_block_iff _ _).mp ht))

/-- **Position I, read on the incoming cover.**  If the two retained classes
sit in different classes at the trivalent endpoint then, their cardinalities
summing to `|A₀|`, those classes are exactly `e_β` and `e_γ` and they tile
`A₀`. -/
theorem high_classes_of_separate
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1)
    (hSeparate : ¬(data.vertexPartition o.high).Rel o.betaAnchor o.gammaAnchor) :
    Disjoint ((data.edgePartition o.betaEdge).block o.betaAnchor)
        ((data.edgePartition o.gammaEdge).block o.gammaAnchor) ∧
      ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
        ((data.edgePartition o.betaEdge).Rel o.betaAnchor sheet ∧
            (data.vertexPartition o.high).block sheet =
              (data.edgePartition o.betaEdge).block o.betaAnchor) ∨
          (¬(data.edgePartition o.betaEdge).Rel o.betaAnchor sheet ∧
            (data.vertexPartition o.high).block sheet =
              (mergedPartition data a b).block input.distinguishedBlock.1 \
                (data.edgePartition o.betaEdge).block o.betaAnchor) := by
  classical
  have hDisjHigh : Disjoint ((data.vertexPartition o.high).block o.betaAnchor)
      ((data.vertexPartition o.high).block o.gammaAnchor) := by
    rw [Finset.disjoint_left]
    intro t hBeta hGamma
    exact hSeparate ((((data.vertexPartition o.high).mem_block_iff _ _).mp hBeta).trans
      ((((data.vertexPartition o.high).mem_block_iff _ _).mp hGamma)).symm)
  have hBetaSub := o.beta_subset_high_block
  have hGammaSub := o.gamma_subset_high_block
  have hBetaWall := o.high_block_subset o.betaAnchor o.beta_rel
  have hGammaWall := o.high_block_subset o.gammaAnchor o.gamma_rel
  have hUnionSub : (data.vertexPartition o.high).block o.betaAnchor ∪
      (data.vertexPartition o.high).block o.gammaAnchor ⊆
      (mergedPartition data a b).block input.distinguishedBlock.1 :=
    Finset.union_subset hBetaWall hGammaWall
  have hUnionCard := Finset.card_union_of_disjoint hDisjHigh
  have hLeSub := Finset.card_le_card hUnionSub
  have hBetaCard := Finset.card_le_card hBetaSub
  have hGammaCard := Finset.card_le_card hGammaSub
  have hIndex := o.beta_gamma_index_sum hAlphaIndex
  have hBetaEq : (data.vertexPartition o.high).block o.betaAnchor =
      (data.edgePartition o.betaEdge).block o.betaAnchor := by
    refine (Finset.eq_of_subset_of_card_le hBetaSub ?_).symm
    unfold SheetPartition.blockCard at hIndex
    omega
  have hGammaEq : (data.vertexPartition o.high).block o.gammaAnchor =
      (data.edgePartition o.gammaEdge).block o.gammaAnchor := by
    refine (Finset.eq_of_subset_of_card_le hGammaSub ?_).symm
    unfold SheetPartition.blockCard at hIndex
    omega
  have hUnionEq : (data.vertexPartition o.high).block o.betaAnchor ∪
      (data.vertexPartition o.high).block o.gammaAnchor =
      (mergedPartition data a b).block input.distinguishedBlock.1 := by
    refine Finset.eq_of_subset_of_card_le hUnionSub ?_
    unfold SheetPartition.blockCard at hIndex
    omega
  have hDisj : Disjoint ((data.edgePartition o.betaEdge).block o.betaAnchor)
      ((data.edgePartition o.gammaEdge).block o.gammaAnchor) := by
    rw [← hBetaEq, ← hGammaEq]; exact hDisjHigh
  refine ⟨hDisj, fun sheet hSheet ↦ ?_⟩
  have hMem : sheet ∈ (data.vertexPartition o.high).block o.betaAnchor ∪
      (data.vertexPartition o.high).block o.gammaAnchor := by
    rw [hUnionEq]
    exact ((mergedPartition data a b).mem_block_iff _ _).mpr hSheet
  rcases Finset.mem_union.mp hMem with hBeta | hGamma
  · refine Or.inl ⟨?_, ?_⟩
    · exact ((data.edgePartition o.betaEdge).mem_block_iff _ _).mp (hBetaEq ▸ hBeta)
    · rw [← hBetaEq]
      exact ((data.vertexPartition o.high).block_eq_of_rel
        (((data.vertexPartition o.high).mem_block_iff _ _).mp hBeta)).symm
  · have hNotBeta : sheet ∉ (data.edgePartition o.betaEdge).block o.betaAnchor := by
      rw [← hBetaEq]
      exact Finset.disjoint_right.mp hDisjHigh hGamma
    refine Or.inr ⟨fun hRel ↦ hNotBeta
      (((data.edgePartition o.betaEdge).mem_block_iff _ _).mpr hRel), ?_⟩
    have hBlock : (data.vertexPartition o.high).block sheet =
        (data.vertexPartition o.high).block o.gammaAnchor :=
      ((data.vertexPartition o.high).block_eq_of_rel
        (((data.vertexPartition o.high).mem_block_iff _ _).mp hGamma)).symm
    rw [hBlock, ← hBetaEq]
    refine Finset.Subset.antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    · exact Finset.mem_sdiff.mpr ⟨hGammaWall ht, Finset.disjoint_right.mp hDisjHigh ht⟩
    · obtain ⟨htWall, htNot⟩ := Finset.mem_sdiff.mp ht
      have hMemUnion : t ∈ (data.vertexPartition o.high).block o.betaAnchor ∪
          (data.vertexPartition o.high).block o.gammaAnchor := by
        rw [hUnionEq]; exact htWall
      rcases Finset.mem_union.mp hMemUnion with h | h
      · exact absurd h htNot
      · exact h

end Orientation

/-! ## §9  The `α = 4` dichotomy, Position II.b branch -/

namespace Orientation

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1}
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  {input : W3SourceInput (contractDatum data hc hab hOne) star}
  (o : Orientation data hc hab hOne input)

/-- A class at the trivalent endpoint meeting neither `e_β` nor `e_γ` is a
singleton: Case `(r0-nd3)` of the local properties at an unramified trivalent
vertex leaves it no room. -/
theorem high_off_block_card_eq_one
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (block : (data.vertexPartition o.high).Blocks)
    (hWall : (mergedPartition data a b).Rel input.distinguishedBlock.1 block.1)
    (hBeta : ¬(data.vertexPartition o.high).Rel o.betaAnchor block.1)
    (hGamma : ¬(data.vertexPartition o.high).Rel o.gammaAnchor block.1) :
    (data.vertexPartition o.high).blockCard block.1 = 1 := by
  classical
  have hRam := localRamification_eq_zero_of_targetChange data fullDim.valid o.high
    o.high_change block
  rw [localRamification_of_triple data o.high contracted o.betaEdge o.gammaEdge
    (Ne.symm (unfoldEdge_ne_contracted hc hab hOne _))
    (Ne.symm (unfoldEdge_ne_contracted hc hab hOne _)) o.beta_ne_gamma_edge
    o.high_star block] at hRam
  have hWallOf : ∀ sheet, (data.vertexPartition o.high).Rel block.1 sheet →
      (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet :=
    fun sheet hRel ↦ hWall.trans (o.refines_high.rel hRel)
  have hBetaCount : (data.edgePartition o.betaEdge).blockCountWithin
      (data.vertexPartition o.high) block.1 =
      (data.vertexPartition o.high).blockCard block.1 := by
    refine blockCountWithin_eq_blockCard_of_singletons _ _ o.beta_refines_high block.1
      (fun sheet hRel ↦ o.beta_singletons' sheet (hWallOf sheet hRel) ?_)
    intro hEdge
    exact hBeta ((o.beta_refines_high.rel hEdge).trans hRel.symm)
  have hGammaCount : (data.edgePartition o.gammaEdge).blockCountWithin
      (data.vertexPartition o.high) block.1 =
      (data.vertexPartition o.high).blockCard block.1 := by
    refine blockCountWithin_eq_blockCard_of_singletons _ _ o.gamma_refines_high block.1
      (fun sheet hRel ↦ o.gamma_singletons' sheet (hWallOf sheet hRel) ?_)
    intro hEdge
    exact hGamma ((o.gamma_refines_high.rel hEdge).trans hRel.symm)
  have hPos := SheetPartition.blockCountWithin_pos (data.edgePartition contracted)
    (data.vertexPartition o.high) block.1
  have hCardPos := (data.vertexPartition o.high).blockCard_pos block.1
  rw [hBetaCount, hGammaCount] at hRam
  omega

/-- **Position II.b, read on the incoming cover.**  If the two retained classes
share a class at the trivalent endpoint then exactly one sheet of `A₀` is
detached from it, and that sheet lies outside both `e_β` and `e_γ`. -/
theorem high_classes_of_shared
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1)
    (hShared : (data.vertexPartition o.high).Rel o.betaAnchor o.gammaAnchor) :
    ∃ x : Fin degree,
      (mergedPartition data a b).Rel input.distinguishedBlock.1 x ∧
      ¬(data.edgePartition o.betaEdge).Rel o.betaAnchor x ∧
      ¬(data.edgePartition o.gammaEdge).Rel o.gammaAnchor x ∧
      (data.vertexPartition o.high).block o.betaAnchor =
        ((mergedPartition data a b).block input.distinguishedBlock.1).erase x ∧
      ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
        (sheet = x ∧ (data.vertexPartition o.high).block sheet = {x}) ∨
          (sheet ≠ x ∧ (data.vertexPartition o.high).block sheet =
            ((mergedPartition data a b).block input.distinguishedBlock.1).erase x) := by
  classical
  set blocks := SheetPartition.blocksWithin (data.vertexPartition o.high)
    (mergedPartition data a b) (wallBlock data hc hab hOne input) with hBlocks
  have hCard : blocks.card = 2 := by
    rw [hBlocks, SheetPartition.card_blocksWithin_eq_blockCountWithin _ _ o.refines_high,
      wallBlock_val]
    exact o.high_count_eq_two fullDim hForest hAlphaIndex
  have hBetaMem : (data.vertexPartition o.high).toBlock o.betaAnchor ∈ blocks := by
    rw [hBlocks, SheetPartition.mem_blocksWithin]
    refine (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel _ _ _ _).mpr ?_
    exact o.beta_rel.trans (o.refines_high.rel
      ((data.vertexPartition o.high).rel_repr_right o.betaAnchor))
  obtain ⟨other, hOtherMem, hOtherNe⟩ :=
    Finset.exists_mem_ne (by omega : 1 < blocks.card)
      ((data.vertexPartition o.high).toBlock o.betaAnchor)
  have hOtherWall : (mergedPartition data a b).Rel input.distinguishedBlock.1 other.1 := by
    have := (SheetPartition.mem_blocksWithin _ _ _ _).mp (hBlocks ▸ hOtherMem)
    exact (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel _ _ _ _).mp this
  have hOtherNotBeta : ¬(data.vertexPartition o.high).Rel o.betaAnchor other.1 := by
    intro hRel
    refine hOtherNe (Subtype.ext ?_)
    change other.1 = (data.vertexPartition o.high).repr o.betaAnchor
    rw [hRel, other.2]
  have hOtherNotGamma : ¬(data.vertexPartition o.high).Rel o.gammaAnchor other.1 :=
    fun hRel ↦ hOtherNotBeta (hShared.trans hRel)
  have hOtherCard := o.high_off_block_card_eq_one fullDim other hOtherWall hOtherNotBeta
    hOtherNotGamma
  have hSetEq : ({(data.vertexPartition o.high).toBlock o.betaAnchor, other} :
      Finset (data.vertexPartition o.high).Blocks) = blocks := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro block hBlock
      rcases Finset.mem_insert.mp hBlock with rfl | hBlock
      · exact hBetaMem
      · rw [Finset.mem_singleton.mp hBlock]; exact hOtherMem
    · rw [hCard, Finset.card_pair (Ne.symm hOtherNe)]
  have hSum := StableLocalProperties.sum_blockCard_blocksWithin (data.vertexPartition o.high)
    (mergedPartition data a b) o.refines_high (wallBlock data hc hab hOne input)
  rw [← hBlocks, ← hSetEq, Finset.sum_pair (Ne.symm hOtherNe), wallBlock_val] at hSum
  have hBetaReprCard : (data.vertexPartition o.high).blockCard
      ((data.vertexPartition o.high).toBlock o.betaAnchor).1 =
      (data.vertexPartition o.high).blockCard o.betaAnchor :=
    ContractionRamification.blockCard_congr _
      ((data.vertexPartition o.high).rel_repr_left o.betaAnchor)
  rw [hBetaReprCard, hOtherCard] at hSum
  have hBetaCardNat : (data.vertexPartition o.high).blockCard o.betaAnchor + 1 =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1 := by
    exact_mod_cast hSum
  refine ⟨other.1, hOtherWall, ?_, ?_, ?_, ?_⟩
  · intro hRel
    exact hOtherNotBeta (o.beta_refines_high.rel hRel)
  · intro hRel
    exact hOtherNotGamma (o.gamma_refines_high.rel hRel)
  · refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro t ht
      refine Finset.mem_erase.mpr ⟨?_, o.high_block_subset o.betaAnchor o.beta_rel ht⟩
      intro hEq
      exact hOtherNotBeta (hEq ▸ ((data.vertexPartition o.high).mem_block_iff _ _).mp ht)
    · rw [Finset.card_erase_of_mem
        (((mergedPartition data a b).mem_block_iff _ _).mpr hOtherWall)]
      have hCardBeta : ((data.vertexPartition o.high).block o.betaAnchor).card =
        (data.vertexPartition o.high).blockCard o.betaAnchor := rfl
      have hCardWall : ((mergedPartition data a b).block input.distinguishedBlock.1).card =
        (mergedPartition data a b).blockCard input.distinguishedBlock.1 := rfl
      omega
  · intro sheet hSheet
    by_cases hEq : sheet = other.1
    · refine Or.inl ⟨hEq, ?_⟩
      rw [hEq]
      exact (data.vertexPartition o.high).block_eq_singleton_of_blockCard_eq_one other.1
        hOtherCard
    · refine Or.inr ⟨hEq, ?_⟩
      have hBetaBlock : (data.vertexPartition o.high).block o.betaAnchor =
          ((mergedPartition data a b).block input.distinguishedBlock.1).erase other.1 := by
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro t ht
          refine Finset.mem_erase.mpr ⟨?_, o.high_block_subset o.betaAnchor o.beta_rel ht⟩
          intro hEqT
          exact hOtherNotBeta (hEqT ▸ ((data.vertexPartition o.high).mem_block_iff _ _).mp ht)
        · rw [Finset.card_erase_of_mem
            (((mergedPartition data a b).mem_block_iff _ _).mpr hOtherWall)]
          have hCardBeta : ((data.vertexPartition o.high).block o.betaAnchor).card =
            (data.vertexPartition o.high).blockCard o.betaAnchor := rfl
          have hCardWall : ((mergedPartition data a b).block input.distinguishedBlock.1).card =
            (mergedPartition data a b).blockCard input.distinguishedBlock.1 := rfl
          omega
      rw [← hBetaBlock]
      refine ((data.vertexPartition o.high).block_eq_of_rel ?_).symm
      have hMem : sheet ∈ ((mergedPartition data a b).block
          input.distinguishedBlock.1).erase other.1 :=
        Finset.mem_erase.mpr ⟨hEq,
          ((mergedPartition data a b).mem_block_iff _ _).mpr hSheet⟩
      rw [← hBetaBlock] at hMem
      exact ((data.vertexPartition o.high).mem_block_iff _ _).mp hMem

end Orientation

/-! ## §10  The `α = 2` orientation: Position II.a at the divalent endpoint -/

namespace Orientation

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1}
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  {input : W3SourceInput (contractDatum data hc hab hOne) star}
  (o : Orientation data hc hab hOne input)

/-- With `k_γ = |A₀|` the full-degree class fills the whole distinguished wall
block. -/
theorem gamma_block_eq_wall
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.edgePartition o.gammaEdge).block o.gammaAnchor =
      (mergedPartition data a b).block input.distinguishedBlock.1 :=
  Finset.eq_of_subset_of_card_le o.gamma_block_subset (le_of_eq hGammaIndex.symm)

theorem gamma_rel_of_wall
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.vertexPartition o.high).Rel o.gammaAnchor sheet := by
  refine o.gamma_refines_high.rel
    (((data.edgePartition o.gammaEdge).mem_block_iff _ _).mp ?_)
  rw [o.gamma_block_eq_wall hGammaIndex]
  exact ((mergedPartition data a b).mem_block_iff _ _).mpr hSheet

/-- **Position II.a, right class.**  The trivalent original endpoint carries
the whole merged wall block. -/
theorem high_block_eq_wall
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.vertexPartition o.high).block sheet = (mergedPartition data a b).block sheet := by
  refine Finset.Subset.antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · exact ((mergedPartition data a b).mem_block_iff _ _).mpr
      (o.refines_high.rel (((data.vertexPartition o.high).mem_block_iff _ _).mp ht))
  · refine ((data.vertexPartition o.high).mem_block_iff _ _).mpr ?_
    have hFirst := o.gamma_rel_of_wall hGammaIndex sheet hSheet
    have hSecond := o.gamma_rel_of_wall hGammaIndex t
      (hSheet.trans (((mergedPartition data a b).mem_block_iff _ _).mp ht))
    exact hFirst.symm.trans hSecond

theorem high_blockCard_eq_wall
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.vertexPartition o.high).blockCard input.distinguishedBlock.1 =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1 := by
  unfold SheetPartition.blockCard
  rw [o.high_block_eq_wall hGammaIndex _ rfl]

theorem high_blockCount_eq_one
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.vertexPartition o.high).blockCountWithin (mergedPartition data a b)
      input.distinguishedBlock.1 = 1 :=
  blockCountWithin_eq_one_of_block_eq _ _ _ (o.high_block_eq_wall hGammaIndex _ rfl)

theorem gamma_blockCount_eq_one
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.edgePartition o.gammaEdge).blockCountWithin (data.vertexPartition o.high)
      input.distinguishedBlock.1 = 1 := by
  refine blockCountWithin_eq_one_of_block_eq _ _ _ ?_
  have hRel : (data.edgePartition o.gammaEdge).Rel o.gammaAnchor
      input.distinguishedBlock.1 := by
    refine ((data.edgePartition o.gammaEdge).mem_block_iff _ _).mp ?_
    rw [o.gamma_block_eq_wall hGammaIndex]
    exact (mergedPartition data a b).self_mem_block _
  rw [← (data.edgePartition o.gammaEdge).block_eq_of_rel hRel,
    o.gamma_block_eq_wall hGammaIndex, o.high_block_eq_wall hGammaIndex _ rfl]

/-- `e_β` sits inside the trivalent endpoint's one class, and off it the
direction `t_β` is singleton-refined. -/
theorem beta_count_of_gamma_full
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.edgePartition o.betaEdge).blockCountWithin (data.vertexPartition o.high)
        input.distinguishedBlock.1 +
      (data.edgePartition o.betaEdge).blockCard o.betaAnchor =
    (mergedPartition data a b).blockCard input.distinguishedBlock.1 + 1 := by
  have hBig : (data.vertexPartition o.high).Rel input.distinguishedBlock.1 o.betaAnchor := by
    refine ((data.vertexPartition o.high).mem_block_iff _ _).mp ?_
    rw [o.high_block_eq_wall hGammaIndex _ rfl]
    exact ((mergedPartition data a b).mem_block_iff _ _).mpr o.beta_rel
  have hCount := W3FourSourceCandidates.blockCountWithin_of_singletons_off_block
    (data.edgePartition o.betaEdge) (data.vertexPartition o.high) o.beta_refines_high
    input.distinguishedBlock.1 o.betaAnchor hBig
    (fun sheet hSheet hNe ↦ o.beta_singletons' sheet (o.refines_high.rel hSheet) hNe)
  rw [o.high_blockCard_eq_wall hGammaIndex] at hCount
  exact hCount

/-- **The number of new occurrences in the `α = 2` orientation.**  Case
`(r0-nd3)` at the unramified trivalent endpoint, whose only class over `A₀` is
`A₀` itself, counts them as `k_β`. -/
theorem contracted_count_of_gamma_full
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.edgePartition contracted).blockCountWithin (mergedPartition data a b)
        input.distinguishedBlock.1 =
      (data.edgePartition o.betaEdge).blockCard o.betaAnchor := by
  have hRam := localRamification_eq_zero_of_targetChange data fullDim.valid o.high
    o.high_change ((data.vertexPartition o.high).toBlock input.distinguishedBlock.1)
  rw [localRamification_of_triple data o.high contracted o.betaEdge o.gammaEdge
    (Ne.symm (unfoldEdge_ne_contracted hc hab hOne _))
    (Ne.symm (unfoldEdge_ne_contracted hc hab hOne _)) o.beta_ne_gamma_edge
    o.high_star _] at hRam
  have hC : ∀ p : SheetPartition degree,
      p.blockCountWithin (data.vertexPartition o.high)
          ((data.vertexPartition o.high).toBlock input.distinguishedBlock.1).1 =
        p.blockCountWithin (data.vertexPartition o.high) input.distinguishedBlock.1 :=
    fun p ↦ ContractionRamification.blockCountWithin_congr p _
      ((data.vertexPartition o.high).rel_repr_left input.distinguishedBlock.1)
  have hCard : (data.vertexPartition o.high).blockCard
      ((data.vertexPartition o.high).toBlock input.distinguishedBlock.1).1 =
      (data.vertexPartition o.high).blockCard input.distinguishedBlock.1 :=
    ContractionRamification.blockCard_congr _
      ((data.vertexPartition o.high).rel_repr_left input.distinguishedBlock.1)
  have hCoarse : (data.edgePartition contracted).blockCountWithin
      (data.vertexPartition o.high) input.distinguishedBlock.1 =
      (data.edgePartition contracted).blockCountWithin (mergedPartition data a b)
        input.distinguishedBlock.1 :=
    blockCountWithin_congr_coarse _ _ _ _ (o.high_block_eq_wall hGammaIndex _ rfl)
  simp only [hC, hCard] at hRam
  rw [o.gamma_blockCount_eq_one hGammaIndex, o.high_blockCard_eq_wall hGammaIndex,
    hCoarse] at hRam
  have hBeta := o.beta_count_of_gamma_full hGammaIndex
  omega

theorem low_count_of_gamma_full
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.vertexPartition o.low).blockCountWithin (mergedPartition data a b)
        input.distinguishedBlock.1 =
      (data.edgePartition o.betaEdge).blockCard o.betaAnchor := by
  have hForestCount := contractionForest_count data hc hForest
    (wallBlock data hc hab hOne input)
  simp only [wallBlock_val] at hForestCount
  have hHighOne := o.high_blockCount_eq_one hGammaIndex
  have hCount := o.contracted_count_of_gamma_full fullDim hGammaIndex
  rcases o.low_mem with hL | hL <;> rcases o.high_mem with hH | hH
  · exact absurd (hL.trans hH.symm) o.low_ne_high
  · rw [hH] at hHighOne; rw [hL]; omega
  · rw [hH] at hHighOne; rw [hL]; omega
  · exact absurd (hL.trans hH.symm) o.low_ne_high

/-- **The new occurrence and the divalent endpoint carry the same classes.** -/
theorem contracted_block_eq_low
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition contracted).block sheet =
      (data.vertexPartition o.low).block sheet :=
  block_eq_of_blockCountWithin_eq (data.edgePartition contracted)
    (data.vertexPartition o.low) (mergedPartition data a b) o.contracted_refines_low
    o.refines_low (wallBlock data hc hab hOne input)
    (by
      simp only [wallBlock_val]
      rw [o.contracted_count_of_gamma_full fullDim hGammaIndex,
        o.low_count_of_gamma_full fullDim hForest hGammaIndex])
    sheet hSheet

/-- `|A'| = k_α + 1`: Position II.a's cardinality, read on the incoming
cover. -/
theorem low_alpha_blockCard
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (data.vertexPartition o.low).blockCard o.alphaAnchor =
      (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor + 1 := by
  have hCount := o.low_blockCount fullDim
  have hLow := o.low_count_of_gamma_full fullDim hForest hGammaIndex
  have hSum := o.index_sum'
  omega

/-- **Position II.a's transferred sheet, produced by the cover.**  The divalent
endpoint's class is `e_α` together with exactly one further sheet of `A₀`. -/
theorem exists_extraSheet
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    ∃ y : Fin degree,
      (mergedPartition data a b).Rel input.distinguishedBlock.1 y ∧
      ¬(data.edgePartition o.alphaEdge).Rel o.alphaAnchor y ∧
      (data.vertexPartition o.low).block o.alphaAnchor =
        insert y ((data.edgePartition o.alphaEdge).block o.alphaAnchor) := by
  classical
  have hSub : (data.edgePartition o.alphaEdge).block o.alphaAnchor ⊆
      (data.vertexPartition o.low).block o.alphaAnchor := by
    intro t ht
    exact ((data.vertexPartition o.low).mem_block_iff _ _).mpr
      (o.alpha_refines_low.rel (((data.edgePartition o.alphaEdge).mem_block_iff _ _).mp ht))
  have hCards := o.low_alpha_blockCard fullDim hForest hGammaIndex
  have hNe : (data.edgePartition o.alphaEdge).block o.alphaAnchor ≠
      (data.vertexPartition o.low).block o.alphaAnchor := by
    intro hEq
    have hCard : ((data.edgePartition o.alphaEdge).block o.alphaAnchor).card =
      ((data.vertexPartition o.low).block o.alphaAnchor).card := by rw [hEq]
    unfold SheetPartition.blockCard at hCards
    omega
  obtain ⟨y, hyMem, hyNot⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hSub, hNe⟩)
  refine ⟨y, ?_, ?_, ?_⟩
  · refine ((mergedPartition data a b).mem_block_iff _ _).mp ?_
    refine Finset.mem_of_subset ?_ hyMem
    intro t ht
    exact ((mergedPartition data a b).mem_block_iff _ _).mpr
      (o.alpha_rel.trans (o.refines_low.rel
        (((data.vertexPartition o.low).mem_block_iff _ _).mp ht)))
  · exact fun hRel ↦ hyNot
      (((data.edgePartition o.alphaEdge).mem_block_iff _ _).mpr hRel)
  · refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset hyMem hSub) ?_).symm
    rw [Finset.card_insert_of_notMem hyNot]
    unfold SheetPartition.blockCard at hCards
    omega

/-- **Position II.a's left class, as the member's own `mergeBlocks`.**  With
the transferred sheet `y` named, the divalent endpoint's classes over `A₀` are
literally `e_α ∪ {y}` and singletons, which is
`W3FourSourceCandidates.GrowProfile.growPartition` at `y`. -/
theorem low_block_eq_mergeBlocks
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (y : Fin degree)
    (hyWall : (mergedPartition data a b).Rel input.distinguishedBlock.1 y)
    (hySep : ¬(data.edgePartition o.alphaEdge).Rel o.alphaAnchor y)
    (hBlock : (data.vertexPartition o.low).block o.alphaAnchor =
      insert y ((data.edgePartition o.alphaEdge).block o.alphaAnchor))
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet) :
    (data.vertexPartition o.low).block sheet =
      ((data.edgePartition o.alphaEdge).mergeBlocks o.alphaAnchor y hySep).block sheet := by
  classical
  have hySingleton : (data.edgePartition o.alphaEdge).block y = {y} :=
    (data.edgePartition o.alphaEdge).block_eq_singleton_of_blockCard_eq_one y
      (o.alpha_singletons' y hyWall hySep)
  have hyLow : (data.vertexPartition o.low).Rel o.alphaAnchor y := by
    refine ((data.vertexPartition o.low).mem_block_iff _ _).mp ?_
    rw [hBlock]
    exact Finset.mem_insert_self _ _
  by_cases hRel : (data.vertexPartition o.low).Rel o.alphaAnchor sheet
  · have hLeft : (data.vertexPartition o.low).block sheet =
        insert y ((data.edgePartition o.alphaEdge).block o.alphaAnchor) := by
      rw [← hBlock]
      exact ((data.vertexPartition o.low).block_eq_of_rel hRel).symm
    have hMergeRel : ((data.edgePartition o.alphaEdge).mergeBlocks o.alphaAnchor y
        hySep).Rel o.alphaAnchor sheet := by
      rw [SheetPartition.mergeBlocks_rel_first_iff]
      have hMem : sheet ∈ insert y ((data.edgePartition o.alphaEdge).block o.alphaAnchor) := by
        rw [← hLeft]
        exact (data.vertexPartition o.low).self_mem_block sheet
      rcases Finset.mem_insert.mp hMem with hEq | hMem
      · rw [hEq]; exact Or.inr rfl
      · exact Or.inl (((data.edgePartition o.alphaEdge).mem_block_iff _ _).mp hMem)
    rw [hLeft, ← ((data.edgePartition o.alphaEdge).mergeBlocks o.alphaAnchor y
      hySep).block_eq_of_rel hMergeRel,
      SheetPartition.mergeBlocks_block_first, hySingleton]
    rw [Finset.union_comm, Finset.insert_eq]
  · have hRight : (data.vertexPartition o.low).block sheet = {sheet} :=
      o.low_block_singleton fullDim sheet hSheet hRel
    have hNotAlpha : ¬(data.edgePartition o.alphaEdge).Rel sheet o.alphaAnchor := by
      intro hEdge
      exact hRel (o.alpha_refines_low.rel hEdge).symm
    have hNotY : ¬(data.edgePartition o.alphaEdge).Rel sheet y := by
      intro hEdge
      have hMem : sheet ∈ (data.edgePartition o.alphaEdge).block y := by
        rw [SheetPartition.mem_block_iff]
        exact hEdge.symm
      rw [hySingleton, Finset.mem_singleton] at hMem
      exact hRel (hMem ▸ hyLow)
    rw [hRight, SheetPartition.mergeBlocks_block_of_separate _ _ _ _ hySep hNotAlpha hNotY]
    exact ((data.edgePartition o.alphaEdge).block_eq_singleton_of_blockCard_eq_one sheet
      (o.alpha_singletons' sheet hSheet (fun h ↦ hNotAlpha h.symm))).symm

end Orientation

/-! ## §12  Building the picture from the classification payload -/

section Build

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

omit hForest hCompat in
/-- A survivor's anchor lies in the distinguished merged wall block. -/
theorem survivor_anchor_rel
    (edge : IncidentSourceEdge (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
        input.distinguishedBlock)) :
    (mergedPartition data a b).Rel input.distinguishedBlock.1 edge.1.1.2 := by
  refine (W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mpr ?_
  have hRel := ((incident_iff_target_mem_and_rel (contractDatum data hc hab hOne)
    edge.1 _).mp edge.2).2
  exact (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_right
    input.distinguishedBlock.1).trans hRel

include hForest hCompat

/-- **The picture, assembled.**  Every field is supplied by the classification
payload: the three survivors of `A₀` with their distinct directions, the
singleton census off each survivor's class, the index sum, the wall's
non-dangling valency and the placement of the divalent occurrence. -/
noncomputable def orientationOfSurvivors
    (low high : target.V)
    (hLowMem : low = a ∨ low = b) (hHighMem : high = a ∨ high = b)
    (hLowNeHigh : low ≠ high)
    (hLowCard : (GluingDatum.incidentEdges low).card = 2)
    (hHighCard : (GluingDatum.incidentEdges high).card = 3)
    (hLowChange : data.targetChange low = 1) (hHighChange : data.targetChange high = 0)
    (alphaSurvivor betaSurvivor gammaSurvivor :
      IncidentSourceEdge (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
          input.distinguishedBlock))
    (hAlphaBeta : alphaSurvivor.1.1.1 ≠ betaSurvivor.1.1.1)
    (hAlphaGamma : alphaSurvivor.1.1.1 ≠ gammaSurvivor.1.1.1)
    (hBetaGamma : betaSurvivor.1.1.1 ≠ gammaSurvivor.1.1.1)
    (hAlphaAtLow : unfoldEdge hc hab hOne alphaSurvivor.1.1.1 ∈
      GluingDatum.incidentEdges low)
    (hBetaAtHigh : unfoldEdge hc hab hOne betaSurvivor.1.1.1 ∈
      GluingDatum.incidentEdges high)
    (hGammaAtHigh : unfoldEdge hc hab hOne gammaSurvivor.1.1.1 ∈
      GluingDatum.incidentEdges high)
    (hAlphaSingletons : ∀ sheet,
      (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      ¬(data.edgePartition (unfoldEdge hc hab hOne alphaSurvivor.1.1.1)).Rel
        alphaSurvivor.1.1.2 sheet →
      (data.edgePartition (unfoldEdge hc hab hOne alphaSurvivor.1.1.1)).blockCard sheet = 1)
    (hBetaSingletons : ∀ sheet,
      (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      ¬(data.edgePartition (unfoldEdge hc hab hOne betaSurvivor.1.1.1)).Rel
        betaSurvivor.1.1.2 sheet →
      (data.edgePartition (unfoldEdge hc hab hOne betaSurvivor.1.1.1)).blockCard sheet = 1)
    (hGammaSingletons : ∀ sheet,
      (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      ¬(data.edgePartition (unfoldEdge hc hab hOne gammaSurvivor.1.1.1)).Rel
        gammaSurvivor.1.1.2 sheet →
      (data.edgePartition (unfoldEdge hc hab hOne gammaSurvivor.1.1.1)).blockCard sheet = 1)
    (hIndexSum :
      (data.edgePartition (unfoldEdge hc hab hOne alphaSurvivor.1.1.1)).blockCard
          alphaSurvivor.1.1.2 +
        (data.edgePartition (unfoldEdge hc hab hOne betaSurvivor.1.1.1)).blockCard
          betaSurvivor.1.1.2 +
        (data.edgePartition (unfoldEdge hc hab hOne gammaSurvivor.1.1.1)).blockCard
          gammaSurvivor.1.1.2 =
      2 * (mergedPartition data a b).blockCard input.distinguishedBlock.1)
    (hValency : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne (wallBlock data hc hab hOne input)) = 3)
    (hAlphaSurvives : ¬IsDangling (contractDatum data hc hab hOne) alphaSurvivor.1)
    (hEndpoint : W4IncomingRetainedFlags.endpoint data hc hab hOne alphaSurvivor.1 =
      data.sourceEndpoint low alphaSurvivor.1.1.2) :
    Orientation data hc hab hOne input where
  low := low
  high := high
  low_mem := hLowMem
  high_mem := hHighMem
  low_ne_high := hLowNeHigh
  low_card := hLowCard
  high_card := hHighCard
  low_change := hLowChange
  high_change := hHighChange
  alphaTarget := alphaSurvivor.1.1.1
  betaTarget := betaSurvivor.1.1.1
  gammaTarget := gammaSurvivor.1.1.1
  alpha_ne_beta := hAlphaBeta
  alpha_ne_gamma := hAlphaGamma
  beta_ne_gamma := hBetaGamma
  alpha_at_low := hAlphaAtLow
  beta_at_high := hBetaAtHigh
  gamma_at_high := hGammaAtHigh
  alphaAnchor := alphaSurvivor.1.1.2
  betaAnchor := betaSurvivor.1.1.2
  gammaAnchor := gammaSurvivor.1.1.2
  alpha_rel := survivor_anchor_rel data hc hab hOne star input alphaSurvivor
  beta_rel := survivor_anchor_rel data hc hab hOne star input betaSurvivor
  gamma_rel := survivor_anchor_rel data hc hab hOne star input gammaSurvivor
  alpha_singletons := hAlphaSingletons
  beta_singletons := hBetaSingletons
  gamma_singletons := hGammaSingletons
  index_sum := hIndexSum
  activePoint := W4IncomingRetainedFlags.endpoint data hc hab hOne alphaSurvivor.1
  active_filter := by
    classical
    have hIncident : Incident (contractDatum data hc hab hOne) alphaSurvivor.1
        (mergedVertex data hc hab hOne (wallBlock data hc hab hOne input)) := by
      show Incident (contractDatum data hc hab hOne) alphaSurvivor.1
        (mergedVertex data hc hab hOne
          (W3Nd2IncomingSelectedCensus.selectedBlock data hc hab hOne star input))
      rw [← W3Nd2IncomingSelectedCensus.selectedVertex_eq_mergedVertex data hc hab hOne
        star input]
      exact alphaSurvivor.2
    have hActive := W4IncomingRetainedFlags.endpoint_active data hc hab hOne hCompat.1
      (wallBlock data hc hab hOne input) ⟨alphaSurvivor.1, hAlphaSurvives⟩ hIncident
    have hTarget : (W4IncomingRetainedFlags.endpoint data hc hab hOne
        alphaSurvivor.1).1.1 = low := by rw [hEndpoint]; rfl
    have hMemActive : W4IncomingRetainedFlags.endpoint data hc hab hOne alphaSurvivor.1 ∈
        (activeFibreVertices data hc hab hOne
          (mergedVertex data hc hab hOne (wallBlock data hc hab hOne input))).filter
          (fun point ↦ point.1.1 = low) :=
      Finset.mem_filter.mpr ⟨hActive, hTarget⟩
    have hSubset : (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne (wallBlock data hc hab hOne input))).filter
        (fun point ↦ point.1.1 = low) ⊆
        (activeFibreVertices data hc hab hOne
          (mergedVertex data hc hab hOne (wallBlock data hc hab hOne input))).filter
          (fun point ↦ ¬point.1.1 = high) := by
      intro point hPoint
      obtain ⟨hMem, hEq⟩ := Finset.mem_filter.mp hPoint
      exact Finset.mem_filter.mpr ⟨hMem, fun hHigh ↦ hLowNeHigh (hEq.symm.trans hHigh)⟩
    have hLe := (Finset.card_le_card hSubset).trans
      (W3Nd3IncomingCensus.otherSide_card_le_one data hc hab hOne fullDim hForest hCompat
        (wallBlock data hc hab hOne input) hValency high hHighMem hHighChange)
    exact Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hMemActive, fun other hOther ↦ Finset.card_le_one.mp hLe _ hOther _ hMemActive⟩
  active_target := by rw [hEndpoint]; rfl
  active_rel := by
    rw [hEndpoint]
    exact (data.vertexPartition low).rel_repr_left _

end Build

/-! ## §13  From block identities to a `SelectedCensus` -/

section Assembly

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1}
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  {input : W3SourceInput (contractDatum data hc hab hOne) star}
  (o : Orientation data hc hab hOne input)

/-- Which original endpoint is `low`, read off the divalent one. -/
theorem Orientation.low_eq_left (hCard : (GluingDatum.incidentEdges a).card = 2) :
    o.low = a ∧ o.high = b := by
  rcases o.low_mem with hL | hL <;> rcases o.high_mem with hH | hH
  · exact absurd (hL.trans hH.symm) o.low_ne_high
  · exact ⟨hL, hH⟩
  · exfalso
    have hHigh := o.high_card
    rw [hH] at hHigh
    omega
  · exact absurd (hL.trans hH.symm) o.low_ne_high

theorem Orientation.low_eq_right (hCard : (GluingDatum.incidentEdges b).card = 2) :
    o.low = b ∧ o.high = a := by
  rcases o.low_mem with hL | hL <;> rcases o.high_mem with hH | hH
  · exact absurd (hL.trans hH.symm) o.low_ne_high
  · exfalso
    have hHigh := o.high_card
    rw [hH] at hHigh
    omega
  · exact ⟨hL, hH⟩
  · exact absurd (hL.trans hH.symm) o.low_ne_high

/-- **The census assembly.**  Three block identities read at the divalent
original endpoint, at the trivalent one and at the contracted occurrence are
exactly a `W3ShiftIncomingMatching.SelectedCensus`. -/
theorem selectedCensus_of_blocks
    (selectedLeft selectedRight selectedNew : SheetPartition degree)
    (hLeft : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (data.vertexPartition o.low).block sheet = selectedLeft.block sheet)
    (hRight : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (data.vertexPartition o.high).block sheet = selectedRight.block sheet)
    (hNew : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (data.edgePartition contracted).block sheet = selectedNew.block sheet) :
    W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
      selectedLeft selectedRight selectedNew where
  divalentLeft := by
    intro hCard
    obtain ⟨hLow, hHigh⟩ := o.low_eq_left hCard
    rw [hLow] at hLeft
    rw [hHigh] at hRight
    exact ⟨hLeft, hRight, hNew⟩
  divalentRight := by
    intro hCard
    obtain ⟨hLow, hHigh⟩ := o.low_eq_right hCard
    rw [hLow] at hLeft
    rw [hHigh] at hRight
    exact ⟨hLeft, hRight, hNew⟩

end Assembly

/-! ## §14  Figure 28's Position I / Position II.b census, in one orientation -/

section LargestCensus

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1}
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  {input : W3SourceInput (contractDatum data hc hab hOne) star}
  (o : Orientation data hc hab hOne input)

theorem Orientation.beta_refines_wall :
    ((contractDatum data hc hab hOne).edgePartition o.betaTarget).Refines
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) := by
  rw [← W3ShiftIncomingMatching.merged_eq_wall data hc hab hOne]
  exact fun i j h ↦ o.refines_high.rel (o.beta_refines_high.rel h)

theorem Orientation.beta_wall_rel_gamma :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      o.betaAnchor o.gammaAnchor :=
  (W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mp
    (o.beta_rel.symm.trans o.gamma_rel)

/-- **Figure 28's `α = 4` census.**  An incoming `w3Four` cover whose divalent
original endpoint carries the full-degree direction displays either Position
I's two-block split of `A₀` or Position II.b's detached sheet, and in both
cases the whole of `A₀` at the divalent endpoint. -/
theorem classes_of_largest_orientation
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hAlphaIndex : (data.edgePartition o.alphaEdge).blockCard o.alphaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    (∃ hDisjoint : Disjoint ((data.edgePartition o.betaEdge).block o.betaAnchor)
        ((data.edgePartition o.gammaEdge).block o.gammaAnchor),
      W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
        (W3FourClosure.splitAlong
          ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
          ((contractDatum data hc hab hOne).edgePartition o.betaTarget)
          o.betaAnchor o.gammaAnchor o.beta_wall_rel_gamma
          (not_rel_of_disjoint hDisjoint))
        (W3FourClosure.splitAlong
          ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
          ((contractDatum data hc hab hOne).edgePartition o.betaTarget)
          o.betaAnchor o.gammaAnchor o.beta_wall_rel_gamma
          (not_rel_of_disjoint hDisjoint))) ∨
    (∃ x : Fin degree, ∃ hxNe : x ≠ o.betaAnchor,
      ∃ hxRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        x o.betaAnchor,
      ¬((contractDatum data hc hab hOne).edgePartition o.betaTarget).Rel o.betaAnchor x ∧
      ¬((contractDatum data hc hab hOne).edgePartition o.gammaTarget).Rel o.gammaAnchor x ∧
      W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
          x o.betaAnchor hxNe hxRel)
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
          x o.betaAnchor hxNe hxRel)) := by
  classical
  have hLeft : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (data.vertexPartition o.low).block sheet =
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet := by
    intro sheet hSheet
    rw [o.low_block_eq_wall hAlphaIndex sheet hSheet,
      W3ShiftIncomingMatching.merged_block_eq_wall_block data hc hab hOne sheet]
  have hNew : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (data.edgePartition contracted).block sheet =
        (data.vertexPartition o.high).block sheet :=
    o.contracted_block_eq_high fullDim hForest hAlphaIndex
  by_cases hShared : (data.vertexPartition o.high).Rel o.betaAnchor o.gammaAnchor
  · obtain ⟨x, hxWall, hxBeta, hxGamma, hBetaBlock, hAll⟩ :=
      o.high_classes_of_shared fullDim hForest hAlphaIndex hShared
    have hxRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        x o.betaAnchor :=
      (W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mp
        (hxWall.symm.trans o.beta_rel)
    have hxNe : x ≠ o.betaAnchor := by
      intro hEq
      exact hxBeta (hEq ▸ (rfl : (data.edgePartition o.betaEdge).Rel o.betaAnchor o.betaAnchor))
    have hRight : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
        (data.vertexPartition o.high).block sheet =
          (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
            x o.betaAnchor hxNe hxRel).block sheet := by
      intro sheet hSheet
      have hRemainder : (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
          x o.betaAnchor hxNe hxRel).block o.betaAnchor =
          ((mergedPartition data a b).block input.distinguishedBlock.1).erase x := by
        rw [SheetPartition.detachSheet_block_remainder,
          wall_block_eq_root data hc hab hOne input x hxWall]
      rcases hAll sheet hSheet with ⟨hEq, hBlock⟩ | ⟨hNe, hBlock⟩
      · rw [hBlock, hEq, SheetPartition.detachSheet_block_single]
      · rw [hBlock, ← hRemainder]
        refine (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
          x o.betaAnchor hxNe hxRel).block_eq_of_rel ?_
        refine ((((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).detachSheet
          x o.betaAnchor hxNe hxRel).mem_block_iff o.betaAnchor sheet).mp ?_
        rw [hRemainder]
        exact Finset.mem_erase.mpr ⟨hNe,
          ((mergedPartition data a b).mem_block_iff _ _).mpr hSheet⟩
    exact Or.inr ⟨x, hxNe, hxRel, hxBeta, hxGamma,
      selectedCensus_of_blocks o _ _ _ hLeft hRight
        (fun sheet hSheet ↦ (hNew sheet hSheet).trans (hRight sheet hSheet))⟩
  · obtain ⟨hDisj, hAll⟩ := o.high_classes_of_separate hAlphaIndex hShared
    have hSep : ¬((contractDatum data hc hab hOne).edgePartition o.betaTarget).Rel
        o.betaAnchor o.gammaAnchor := not_rel_of_disjoint hDisj
    have hRight : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
        (data.vertexPartition o.high).block sheet =
          (W3FourClosure.splitAlong
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
            ((contractDatum data hc hab hOne).edgePartition o.betaTarget)
            o.betaAnchor o.gammaAnchor o.beta_wall_rel_gamma hSep).block sheet := by
      intro sheet hSheet
      have hWallRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          o.betaAnchor sheet :=
        (W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mp
          (o.beta_rel.symm.trans hSheet)
      rcases hAll sheet hSheet with ⟨hRel, hBlock⟩ | ⟨hRel, hBlock⟩
      · have hRelW : ((contractDatum data hc hab hOne).edgePartition o.betaTarget).Rel
            o.betaAnchor sheet := hRel
        have hSplit : (W3FourClosure.splitAlong
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
            ((contractDatum data hc hab hOne).edgePartition o.betaTarget)
            o.betaAnchor o.gammaAnchor o.beta_wall_rel_gamma hSep).Rel o.betaAnchor sheet := by
          rw [SheetPartition.rel_iff, W3FourClosure.splitAlong_repr_pivot,
            W3FourClosure.splitAlong_repr_eq, ite_eq_left hWallRel, ite_eq_left hRelW]
        rw [hBlock, ← (W3FourClosure.splitAlong _ _ _ _ o.beta_wall_rel_gamma
          hSep).block_eq_of_rel hSplit,
          W3FourClosure.splitAlong_block_pivot o.beta_wall_rel_gamma hSep
            o.beta_refines_wall]
        rfl
      · have hRelW : ¬((contractDatum data hc hab hOne).edgePartition o.betaTarget).Rel
            o.betaAnchor sheet := hRel
        have hSplit : (W3FourClosure.splitAlong
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
            ((contractDatum data hc hab hOne).edgePartition o.betaTarget)
            o.betaAnchor o.gammaAnchor o.beta_wall_rel_gamma hSep).Rel
            o.gammaAnchor sheet := by
          rw [SheetPartition.rel_iff, W3FourClosure.splitAlong_repr_alt,
            W3FourClosure.splitAlong_repr_eq, ite_eq_left hWallRel, ite_eq_right hRelW]
        rw [hBlock, ← (W3FourClosure.splitAlong _ _ _ _ o.beta_wall_rel_gamma
          hSep).block_eq_of_rel hSplit,
          W3FourClosure.splitAlong_block_alt o.beta_wall_rel_gamma hSep,
          wall_block_eq_root data hc hab hOne input o.betaAnchor o.beta_rel]
        rfl
    exact Or.inl ⟨hDisj, selectedCensus_of_blocks o _ _ _ hLeft hRight
      (fun sheet hSheet ↦ (hNew sheet hSheet).trans (hRight sheet hSheet))⟩

end LargestCensus

/-! ## §15  Figure 28's Position II.a census, in one orientation -/

section GrowCensus

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1}
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  {input : W3SourceInput (contractDatum data hc hab hOne) star}
  (o : Orientation data hc hab hOne input)

/-- **Figure 28's `α = 2` census.**  An incoming `w3Four` cover whose divalent
original endpoint carries one of the two smaller directions displays Position
II.a: `e_α` enlarged by one sheet of `A₀` at the divalent endpoint and on the
contracted occurrence, and the whole of `A₀` at the trivalent one. -/
theorem classes_of_grow_orientation
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hGammaIndex : (data.edgePartition o.gammaEdge).blockCard o.gammaAnchor =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1) :
    ∃ y : Fin degree,
      ∃ hSep : ¬((contractDatum data hc hab hOne).edgePartition o.alphaTarget).Rel
        o.alphaAnchor y,
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          input.distinguishedBlock.1 y ∧
        W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
          (((contractDatum data hc hab hOne).edgePartition o.alphaTarget).mergeBlocks
            o.alphaAnchor y hSep)
          ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
          (((contractDatum data hc hab hOne).edgePartition o.alphaTarget).mergeBlocks
            o.alphaAnchor y hSep) := by
  classical
  obtain ⟨y, hyWall, hySep, hBlock⟩ := o.exists_extraSheet fullDim hForest hGammaIndex
  have hSepW : ¬((contractDatum data hc hab hOne).edgePartition o.alphaTarget).Rel
    o.alphaAnchor y := hySep
  refine ⟨y, hSepW,
    (W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mp hyWall, ?_⟩
  have hLeft : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (data.vertexPartition o.low).block sheet =
        (((contractDatum data hc hab hOne).edgePartition o.alphaTarget).mergeBlocks
          o.alphaAnchor y hSepW).block sheet :=
    fun sheet hSheet ↦ o.low_block_eq_mergeBlocks fullDim y hyWall hySep hBlock sheet hSheet
  have hRight : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      (data.vertexPartition o.high).block sheet =
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).block sheet := by
    intro sheet hSheet
    rw [o.high_block_eq_wall hGammaIndex sheet hSheet,
      W3ShiftIncomingMatching.merged_block_eq_wall_block data hc hab hOne sheet]
  exact selectedCensus_of_blocks o _ _ _ hLeft hRight
    (fun sheet hSheet ↦ (o.contracted_block_eq_low fullDim hForest hGammaIndex sheet
      hSheet).trans (hLeft sheet hSheet))

end GrowCensus

/-! ## §16  The two orientations over the classification payload -/

section Sides

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)

/-- With `a` divalent, the isolated direction's original occurrence is at `a`. -/
theorem divalent_unfold_mem_left (hCard : (GluingDatum.incidentEdges a).card = 2) :
    unfoldEdge hc hab hOne (divalentOccurrence data hc hab hOne fullDim star) ∈
      GluingDatum.incidentEdges a :=
  (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
    (W3Nd2IncomingTargetPlacement.divalentOccurrence_spec data hc hab hOne fullDim star).1).mp
    (W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_false data hc hab hOne
      fullDim star hCard)

/-- With `b` divalent, it is at `b`. -/
theorem divalent_unfold_mem_right (hCard : (GluingDatum.incidentEdges b).card = 2) :
    unfoldEdge hc hab hOne (divalentOccurrence data hc hab hOne fullDim star) ∈
      GluingDatum.incidentEdges b :=
  (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp
    (W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_true data hc hab hOne
      fullDim star hCard)

/-- With `a` divalent, every other wall direction is restored at `b`. -/
theorem other_unfold_mem_right (hCard : (GluingDatum.incidentEdges a).card = 2)
    (edge : (contract target hab hOne).edges)
    (hMem : edge ∈ GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V))
    (hNe : edge ≠ divalentOccurrence data hc hab hOne fullDim star) :
    unfoldEdge hc hab hOne edge ∈ GluingDatum.incidentEdges b := by
  refine (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp ?_
  have hSide := W3Nd3IncomingCensus.side_ne_of_ne_divalentOccurrence data hc hab hOne
    fullDim star edge hMem hNe
  rw [W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_false data hc hab hOne
    fullDim star hCard] at hSide
  exact Bool.not_eq_false _ |>.mp hSide

/-- With `b` divalent, every other wall direction is restored at `a`. -/
theorem other_unfold_mem_left (hCard : (GluingDatum.incidentEdges b).card = 2)
    (edge : (contract target hab hOne).edges)
    (hMem : edge ∈ GluingDatum.incidentEdges (⟨a, hab⟩ : (contract target hab hOne).V))
    (hNe : edge ≠ divalentOccurrence data hc hab hOne fullDim star) :
    unfoldEdge hc hab hOne edge ∈ GluingDatum.incidentEdges a := by
  refine (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _ hMem).mp ?_
  have hSide := W3Nd3IncomingCensus.side_ne_of_ne_divalentOccurrence data hc hab hOne
    fullDim star edge hMem hNe
  rw [W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_true data hc hab hOne
    fullDim star hCard] at hSide
  exact Bool.not_eq_true _ |>.mp hSide

/-- With `a` divalent, the isolated direction's canonical endpoint is above `a`. -/
theorem endpoint_eq_left (hCard : (GluingDatum.incidentEdges a).card = 2)
    (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hTarget : edge.1.1 = divalentOccurrence data hc hab hOne fullDim star) :
    W4IncomingRetainedFlags.endpoint data hc hab hOne edge =
      data.sourceEndpoint a edge.1.2 := by
  show data.sourceEndpoint
    (if IncomingTargetExpansion.right hc hab hOne edge.1.1 then b else a) edge.1.2 = _
  rw [hTarget, W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_false data hc hab
    hOne fullDim star hCard]
  rfl

/-- With `b` divalent, it is above `b`. -/
theorem endpoint_eq_right (hCard : (GluingDatum.incidentEdges b).card = 2)
    (edge : (contractDatum data hc hab hOne).SourceEdge)
    (hTarget : edge.1.1 = divalentOccurrence data hc hab hOne fullDim star) :
    W4IncomingRetainedFlags.endpoint data hc hab hOne edge =
      data.sourceEndpoint b edge.1.2 := by
  show data.sourceEndpoint
    (if IncomingTargetExpansion.right hc hab hOne edge.1.1 then b else a) edge.1.2 = _
  rw [hTarget, W3Nd2IncomingMemberMatching.divalentOccurrence_right_eq_true data hc hab
    hOne fullDim star hCard]
  rfl

end Sides

/-! ## §17  The census on the `w3Four` classification payload -/

section Payload

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (hCompat : DanglingCompatible data hc hab hOne)
  (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W3SourceInput (contractDatum data hc hab hOne) star)
  (grown : GrowProfile input)

theorem grow_survives : ¬IsDangling (contractDatum data hc hab hOne) grown.grow.1 := by
  apply (mem_survivors (contractDatum data hc hab hOne) input.distinguishedBlock _).mp
  rw [grown.surviving]
  exact Finset.mem_insert_self _ _

theorem other_survives : ¬IsDangling (contractDatum data hc hab hOne) grown.other.1 := by
  apply (mem_survivors (contractDatum data hc hab hOne) input.distinguishedBlock _).mp
  rw [grown.surviving]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem largest_survives : ¬IsDangling (contractDatum data hc hab hOne) grown.largest.1 := by
  apply (mem_survivors (contractDatum data hc hab hOne) input.distinguishedBlock _).mp
  rw [grown.surviving]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

include grown in
/-- The distinguished wall block has non-dangling valency three. -/
theorem grow_wall_valency :
    nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne (wallBlock data hc hab hOne input)) = 3 := by
  classical
  have hCard : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
        input.distinguishedBlock) = 3 := by
    have hSurv := card_survivors (contractDatum data hc hab hOne) input.distinguishedBlock
    rw [grown.surviving,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact fun h ↦ h.elim grown.grow_ne_other grown.grow_ne_largest),
      Finset.card_pair grown.other_ne_largest] at hSurv
    omega
  show nonDanglingValency (contractDatum data hc hab hOne)
    (mergedVertex data hc hab hOne
      (W3Nd2IncomingSelectedCensus.selectedBlock data hc hab hOne star input)) = 3
  rw [← W3Nd2IncomingSelectedCensus.selectedVertex_eq_mergedVertex data hc hab hOne
    star input]
  exact hCard

theorem largest_blockCard_eq_wall :
    (data.edgePartition (unfoldEdge hc hab hOne grown.largest.1.1.1)).blockCard
        grown.largest.1.1.2 =
      (mergedPartition data a b).blockCard input.distinguishedBlock.1 := by
  rw [W3ShiftIncomingMatching.merged_eq_wall data hc hab hOne]
  exact grown.largest_index

theorem grow_other_blockCard_sum :
    (data.edgePartition (unfoldEdge hc hab hOne grown.grow.1.1.1)).blockCard
        grown.grow.1.1.2 +
      (data.edgePartition (unfoldEdge hc hab hOne grown.other.1.1.1)).blockCard
        grown.other.1.1.2 =
    (mergedPartition data a b).blockCard input.distinguishedBlock.1 := by
  rw [W3ShiftIncomingMatching.merged_eq_wall data hc hab hOne]
  exact grown.index_sum

include fullDim hForest hCompat grown in
/-- **Figure 28's `α = 4` census, on the classification payload.**  An incoming
`w3Four` cover whose isolated direction is the full-degree one is in Position I
or in Position II.b, and displays that member's three classes over `A₀`. -/
theorem classes_of_largest
    (hDiv : divalentOccurrence data hc hab hOne fullDim star = grown.largestTarget) :
    (∃ hDisjoint : Disjoint (((contractDatum data hc hab hOne).edgePartition
          grown.growTarget).block grown.growAnchor)
        (((contractDatum data hc hab hOne).edgePartition grown.otherTarget).block
          grown.otherAnchor),
      W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
        (W3FourClosure.PositionOne.fine
          { toFourStarGeometry := W3FourClosure.ofGrowProfile grown, disjoint := hDisjoint })
        (W3FourClosure.PositionOne.fine
          { toFourStarGeometry := W3FourClosure.ofGrowProfile grown,
            disjoint := hDisjoint })) ∨
    (∃ x : Fin degree,
      ∃ hxWall : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        grown.growAnchor x,
      ∃ hxGrow : ¬((contractDatum data hc hab hOne).edgePartition grown.growTarget).Rel
        grown.growAnchor x,
      ∃ hxOther : ¬((contractDatum data hc hab hOne).edgePartition grown.otherTarget).Rel
        grown.otherAnchor x,
      W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
        (W3FourClosure.PositionTwo.fine
          { toFourStarGeometry := W3FourClosure.ofGrowProfile grown, outside := x,
            outside_wall := hxWall, outside_grow := hxGrow, outside_other := hxOther })
        (W3FourClosure.PositionTwo.fine
          { toFourStarGeometry := W3FourClosure.ofGrowProfile grown, outside := x,
            outside_wall := hxWall, outside_grow := hxGrow,
            outside_other := hxOther })) := by
  classical
  have hIndex := largest_blockCard_eq_wall data hc hab hOne star input grown
  have hSum := grow_other_blockCard_sum data hc hab hOne star input grown
  have hValency := grow_wall_valency data hc hab hOne star input grown
  have hSurvives := largest_survives data hc hab hOne star input grown
  have hAlphaBeta : grown.largest.1.1.1 ≠ grown.grow.1.1.1 :=
    fun h ↦ grown.grow_target_ne_largest h.symm
  have hAlphaGamma : grown.largest.1.1.1 ≠ grown.other.1.1.1 :=
    fun h ↦ grown.other_target_ne_largest h.symm
  have hSingA : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      ¬(data.edgePartition (unfoldEdge hc hab hOne grown.largest.1.1.1)).Rel
        grown.largest.1.1.2 sheet →
      (data.edgePartition (unfoldEdge hc hab hOne grown.largest.1.1.1)).blockCard sheet = 1 :=
    fun sheet hSheet hNe ↦ W3FourSourceCandidates.largest_blockCard_eq_one grown sheet
      ((W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mp hSheet) hNe
  have hSingB : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      ¬(data.edgePartition (unfoldEdge hc hab hOne grown.grow.1.1.1)).Rel
        grown.grow.1.1.2 sheet →
      (data.edgePartition (unfoldEdge hc hab hOne grown.grow.1.1.1)).blockCard sheet = 1 :=
    fun sheet hSheet hNe ↦ W3FourSourceCandidates.grow_blockCard_eq_one grown sheet
      ((W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mp hSheet) hNe
  have hSingC : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      ¬(data.edgePartition (unfoldEdge hc hab hOne grown.other.1.1.1)).Rel
        grown.other.1.1.2 sheet →
      (data.edgePartition (unfoldEdge hc hab hOne grown.other.1.1.1)).blockCard sheet = 1 :=
    fun sheet hSheet hNe ↦ W3FourSourceCandidates.other_blockCard_eq_one grown sheet
      ((W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mp hSheet) hNe
  rcases endpoint_valencies data hc hab hOne fullDim star with
    ⟨hA2, hB3, hChA, hChB⟩ | ⟨hA3, hB2, hChA, hChB⟩
  · have hAlphaLow : unfoldEdge hc hab hOne grown.largestTarget ∈
        GluingDatum.incidentEdges a := by
      rw [← hDiv]
      exact divalent_unfold_mem_left data hc hab hOne fullDim star hA2
    rcases classes_of_largest_orientation
      (orientationOfSurvivors data hc hab hOne fullDim hForest hCompat star input a b
        (Or.inl rfl) (Or.inr rfl) hab hA2 hB3 hChA hChB
        grown.largest grown.grow grown.other hAlphaBeta hAlphaGamma
        grown.grow_target_ne_other hAlphaLow
        (other_unfold_mem_right data hc hab hOne fullDim star hA2 grown.growTarget
          grown.growTarget_mem (fun h ↦ grown.grow_target_ne_largest (h.trans hDiv)))
        (other_unfold_mem_right data hc hab hOne fullDim star hA2 grown.otherTarget
          grown.otherTarget_mem (fun h ↦ grown.other_target_ne_largest (h.trans hDiv)))
        hSingA hSingB hSingC (by omega) hValency hSurvives
        (endpoint_eq_left data hc hab hOne fullDim star hA2 grown.largest.1 hDiv.symm))
      fullDim hForest hIndex with
      ⟨hDisjoint, hCensus⟩ | ⟨x, _hxNe, hxRel, hxGrow, hxOther, hCensus⟩
    · exact Or.inl ⟨hDisjoint, hCensus⟩
    · exact Or.inr ⟨x, hxRel.symm, hxGrow, hxOther, hCensus⟩
  · have hAlphaLow : unfoldEdge hc hab hOne grown.largestTarget ∈
        GluingDatum.incidentEdges b := by
      rw [← hDiv]
      exact divalent_unfold_mem_right data hc hab hOne fullDim star hB2
    rcases classes_of_largest_orientation
      (orientationOfSurvivors data hc hab hOne fullDim hForest hCompat star input b a
        (Or.inr rfl) (Or.inl rfl) (Ne.symm hab) hB2 hA3 hChB hChA
        grown.largest grown.grow grown.other hAlphaBeta hAlphaGamma
        grown.grow_target_ne_other hAlphaLow
        (other_unfold_mem_left data hc hab hOne fullDim star hB2 grown.growTarget
          grown.growTarget_mem (fun h ↦ grown.grow_target_ne_largest (h.trans hDiv)))
        (other_unfold_mem_left data hc hab hOne fullDim star hB2 grown.otherTarget
          grown.otherTarget_mem (fun h ↦ grown.other_target_ne_largest (h.trans hDiv)))
        hSingA hSingB hSingC (by omega) hValency hSurvives
        (endpoint_eq_right data hc hab hOne fullDim star hB2 grown.largest.1 hDiv.symm))
      fullDim hForest hIndex with
      ⟨hDisjoint, hCensus⟩ | ⟨x, _hxNe, hxRel, hxGrow, hxOther, hCensus⟩
    · exact Or.inl ⟨hDisjoint, hCensus⟩
    · exact Or.inr ⟨x, hxRel.symm, hxGrow, hxOther, hCensus⟩

include fullDim hForest hCompat grown in
/-- **Figure 28's `α = 2` census, on the classification payload.**  An incoming
`w3Four` cover whose isolated direction is the grow profile's own smaller one
is in Position II.a, and its transferred sheet `y` is produced. -/
theorem classes_of_grow
    (hDiv : divalentOccurrence data hc hab hOne fullDim star = grown.growTarget) :
    ∃ y : Fin degree,
      ∃ hSep : ¬((contractDatum data hc hab hOne).edgePartition grown.growTarget).Rel
        grown.growAnchor y,
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          input.distinguishedBlock.1 y ∧
        W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
          (((contractDatum data hc hab hOne).edgePartition grown.growTarget).mergeBlocks
            grown.growAnchor y hSep)
          ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
          (((contractDatum data hc hab hOne).edgePartition grown.growTarget).mergeBlocks
            grown.growAnchor y hSep) := by
  classical
  have hIndex := largest_blockCard_eq_wall data hc hab hOne star input grown
  have hSum := grow_other_blockCard_sum data hc hab hOne star input grown
  have hValency := grow_wall_valency data hc hab hOne star input grown
  have hSurvives := grow_survives data hc hab hOne star input grown
  have hSingA : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      ¬(data.edgePartition (unfoldEdge hc hab hOne grown.grow.1.1.1)).Rel
        grown.grow.1.1.2 sheet →
      (data.edgePartition (unfoldEdge hc hab hOne grown.grow.1.1.1)).blockCard sheet = 1 :=
    fun sheet hSheet hNe ↦ W3FourSourceCandidates.grow_blockCard_eq_one grown sheet
      ((W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mp hSheet) hNe
  have hSingB : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      ¬(data.edgePartition (unfoldEdge hc hab hOne grown.other.1.1.1)).Rel
        grown.other.1.1.2 sheet →
      (data.edgePartition (unfoldEdge hc hab hOne grown.other.1.1.1)).blockCard sheet = 1 :=
    fun sheet hSheet hNe ↦ W3FourSourceCandidates.other_blockCard_eq_one grown sheet
      ((W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mp hSheet) hNe
  have hSingC : ∀ sheet, (mergedPartition data a b).Rel input.distinguishedBlock.1 sheet →
      ¬(data.edgePartition (unfoldEdge hc hab hOne grown.largest.1.1.1)).Rel
        grown.largest.1.1.2 sheet →
      (data.edgePartition (unfoldEdge hc hab hOne grown.largest.1.1.1)).blockCard sheet = 1 :=
    fun sheet hSheet hNe ↦ W3FourSourceCandidates.largest_blockCard_eq_one grown sheet
      ((W3ShiftIncomingMatching.merged_rel_iff_wall_rel data hc hab hOne _ _).mp hSheet) hNe
  rcases endpoint_valencies data hc hab hOne fullDim star with
    ⟨hA2, hB3, hChA, hChB⟩ | ⟨hA3, hB2, hChA, hChB⟩
  · have hAlphaLow : unfoldEdge hc hab hOne grown.growTarget ∈
        GluingDatum.incidentEdges a := by
      rw [← hDiv]
      exact divalent_unfold_mem_left data hc hab hOne fullDim star hA2
    exact classes_of_grow_orientation
      (orientationOfSurvivors data hc hab hOne fullDim hForest hCompat star input a b
        (Or.inl rfl) (Or.inr rfl) hab hA2 hB3 hChA hChB
        grown.grow grown.other grown.largest grown.grow_target_ne_other
        grown.grow_target_ne_largest grown.other_target_ne_largest hAlphaLow
        (other_unfold_mem_right data hc hab hOne fullDim star hA2 grown.otherTarget
          grown.otherTarget_mem (fun h ↦ grown.grow_target_ne_other (h.trans hDiv).symm))
        (other_unfold_mem_right data hc hab hOne fullDim star hA2 grown.largestTarget
          grown.largestTarget_mem
          (fun h ↦ grown.grow_target_ne_largest (h.trans hDiv).symm))
        hSingA hSingB hSingC (by omega) hValency hSurvives
        (endpoint_eq_left data hc hab hOne fullDim star hA2 grown.grow.1 hDiv.symm))
      fullDim hForest hIndex
  · have hAlphaLow : unfoldEdge hc hab hOne grown.growTarget ∈
        GluingDatum.incidentEdges b := by
      rw [← hDiv]
      exact divalent_unfold_mem_right data hc hab hOne fullDim star hB2
    exact classes_of_grow_orientation
      (orientationOfSurvivors data hc hab hOne fullDim hForest hCompat star input b a
        (Or.inr rfl) (Or.inl rfl) (Ne.symm hab) hB2 hA3 hChB hChA
        grown.grow grown.other grown.largest grown.grow_target_ne_other
        grown.grow_target_ne_largest grown.other_target_ne_largest hAlphaLow
        (other_unfold_mem_left data hc hab hOne fullDim star hB2 grown.otherTarget
          grown.otherTarget_mem (fun h ↦ grown.grow_target_ne_other (h.trans hDiv).symm))
        (other_unfold_mem_left data hc hab hOne fullDim star hB2 grown.largestTarget
          grown.largestTarget_mem
          (fun h ↦ grown.grow_target_ne_largest (h.trans hDiv).symm))
        hSingA hSingB hSingC (by omega) hValency hSurvives
        (endpoint_eq_right data hc hab hOne fullDim star hB2 grown.grow.1 hDiv.symm))
      fullDim hForest hIndex

include fullDim hForest hCompat in
/-- **The selected-block census, on the classification payload.**  From
`W3IncomingClassification.Classification.four`'s own payload -- an `Nd3Profile`
of the distinguished block with three distinct target directions and the
largest index equal to `|A₀|` -- an incoming `w3Four` cover displays exactly
one of Figure 28's four pictures over the distinguished wall block: Position I's
two-block split of `A₀` or Position II.b's detached sheet when the isolated
direction is `t₄`, and Position II.a with its own transferred sheet when it is
`t₂` or `t₃`.  In the first two the `W3FourClosure.PositionOne` / `PositionTwo`
datum is *produced*; in the last two the transferred sheet `y` is, and it is
matched against `W3FourSourceCandidates.GrowProfile.extraSheet` by
`GrowProfile.withExtra` (see the module docstring). -/
theorem exists_selectedCensus
    (profile : Nd3Profile (contractDatum data hc hab hOne) input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : (contractDatum data hc hab hOne).sourceEdgeIndex profile.largest.1 =
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
        input.distinguishedBlock.1) :
    (divalentOccurrence data hc hab hOne fullDim star = profile.largest.1.1.1 ∧
      ((∃ hDisjoint : Disjoint (((contractDatum data hc hab hOne).edgePartition
            (growProfileFirst profile directions largest_index).growTarget).block
            (growProfileFirst profile directions largest_index).growAnchor)
          (((contractDatum data hc hab hOne).edgePartition
            (growProfileFirst profile directions largest_index).otherTarget).block
            (growProfileFirst profile directions largest_index).otherAnchor),
          W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
            (W3FourClosure.PositionOne.fine
              { toFourStarGeometry := W3FourClosure.ofGrowProfile
                  (growProfileFirst profile directions largest_index),
                disjoint := hDisjoint })
            (W3FourClosure.PositionOne.fine
              { toFourStarGeometry := W3FourClosure.ofGrowProfile
                  (growProfileFirst profile directions largest_index),
                disjoint := hDisjoint })) ∨
        (∃ x : Fin degree,
          ∃ hxWall : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
            (growProfileFirst profile directions largest_index).growAnchor x,
          ∃ hxGrow : ¬((contractDatum data hc hab hOne).edgePartition
            (growProfileFirst profile directions largest_index).growTarget).Rel
            (growProfileFirst profile directions largest_index).growAnchor x,
          ∃ hxOther : ¬((contractDatum data hc hab hOne).edgePartition
            (growProfileFirst profile directions largest_index).otherTarget).Rel
            (growProfileFirst profile directions largest_index).otherAnchor x,
          W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
            (W3FourClosure.PositionTwo.fine
              { toFourStarGeometry := W3FourClosure.ofGrowProfile
                  (growProfileFirst profile directions largest_index),
                outside := x, outside_wall := hxWall, outside_grow := hxGrow,
                outside_other := hxOther })
            (W3FourClosure.PositionTwo.fine
              { toFourStarGeometry := W3FourClosure.ofGrowProfile
                  (growProfileFirst profile directions largest_index),
                outside := x, outside_wall := hxWall, outside_grow := hxGrow,
                outside_other := hxOther })))) ∨
    (divalentOccurrence data hc hab hOne fullDim star = profile.first.1.1.1 ∧
      ∃ y : Fin degree,
      ∃ hSep : ¬((contractDatum data hc hab hOne).edgePartition
          (growProfileFirst profile directions largest_index).growTarget).Rel
          (growProfileFirst profile directions largest_index).growAnchor y,
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
            input.distinguishedBlock.1 y ∧
          W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
            (((contractDatum data hc hab hOne).edgePartition
              (growProfileFirst profile directions largest_index).growTarget).mergeBlocks
              (growProfileFirst profile directions largest_index).growAnchor y hSep)
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
            (((contractDatum data hc hab hOne).edgePartition
              (growProfileFirst profile directions largest_index).growTarget).mergeBlocks
              (growProfileFirst profile directions largest_index).growAnchor y hSep)) ∨
    (divalentOccurrence data hc hab hOne fullDim star = profile.second.1.1.1 ∧
      ∃ y : Fin degree,
      ∃ hSep : ¬((contractDatum data hc hab hOne).edgePartition
          (growProfileSecond profile directions largest_index).growTarget).Rel
          (growProfileSecond profile directions largest_index).growAnchor y,
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
            input.distinguishedBlock.1 y ∧
          W3ShiftIncomingMatching.SelectedCensus data hc hab hOne star input
            (((contractDatum data hc hab hOne).edgePartition
              (growProfileSecond profile directions largest_index).growTarget).mergeBlocks
              (growProfileSecond profile directions largest_index).growAnchor y hSep)
            ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
            (((contractDatum data hc hab hOne).edgePartition
              (growProfileSecond profile directions largest_index).growTarget).mergeBlocks
              (growProfileSecond profile directions largest_index).growAnchor y hSep)) := by
  rcases W3FourIncomingCensus.divalentOccurrence_eq_first_or_second_or_largest data hc hab
      hOne fullDim hForest hCompat star input profile directions largest_index with
    hFirst | hSecond | hLargest
  · exact Or.inr (Or.inl ⟨hFirst, classes_of_grow data hc hab hOne fullDim hForest hCompat
      star input (growProfileFirst profile directions largest_index) hFirst⟩)
  · exact Or.inr (Or.inr ⟨hSecond, classes_of_grow data hc hab hOne fullDim hForest hCompat
      star input (growProfileSecond profile directions largest_index) hSecond⟩)
  · exact Or.inl ⟨hLargest, classes_of_largest data hc hab hOne fullDim hForest hCompat
      star input (growProfileFirst profile directions largest_index) hLargest⟩

end Payload

end DraismaVargas.LocalCases.W3FourSelectedCensus
