import DraismaVargas.Infrastructure.ContractionRamification
import DraismaVargas.LocalCases.WallDegeneration

/-!
# Feeding the four-valent wall interface from a contraction, under the paper's own hypothesis

`FullDimensionalSourcePresentation.false_of_auxR0SourceInput` shows that
`W4StableSource.AuxR0SourceInput data star` cannot be fed from a single datum.
The interface describes the **codimension-one wall datum** (target one
occurrence short, excess `1` at the wall, one more stable path than the wall
target has edges), while a square honest stable presentation describes the
**full-dimensional datum** (change-minimal, one stable path per occurrence).
`WallDegeneration` builds the relation between the two data for the candidate
the library supplies, `GluingContraction.contractDatum`.

This module closes the loop: it produces an `AuxR0SourceInput` for the
**contracted** datum out of a `FullDimensionalSourcePresentation` of the datum
being contracted, plus the contraction receipts.  It is the four-valent (`w4`)
wall of the local case analysis of Draisma–Vargas Part I, arXiv:1909.12924.

## What is proved here, and what is assumed

Proved:

* `targetChange_contractDatum_merge` — Draisma–Vargas Part I,
  `prop-rphi-under-contraction`, *second* conclusion, `ch(w₀) = ch(u) + ch(v)`:
  under `ContractionRamification.ContractionForest` the change at the merged
  target vertex is the sum of the changes at the two contracted endpoints.
  `ContractionRamification` proves the per-block additivity; summing it over the
  blocks of the merged partition is the step taken here.
* `targetExcess_contractDatum_merge` — hence
  `exc(w₀) = exc(u) + exc(v) + 1`, because the merged valency loses the two ends
  of the contracted occurrence (`card_incidentEdges_merge`).
* `targetExcess_contractDatum_merge_eq_one` — **Equation (C) is a theorem, not a
  hypothesis.**  Change-minimality of the full-dimensional datum gives
  `exc(u) = exc(v) = 0`, so `exc(w₀) = 1` exactly.  This is the `equation_c`
  field of `AuxR0SourceInput`, and it is the precise reason the wall datum is
  *not* change-minimal even though the datum it comes from is.
* `sum_targetExcess_contractDatum` — the free global cross-check: the wall
  datum's total dimension correction is `1 + 2(g(source') - g(source))`, so the
  wall datum is one step off saturation, which is what codimension one means.
* `genus_sourceGraph_contractDatum_eq` — hence source-genus preservation is
  *equivalent* to the wall datum being change-minimal away from the wall.  Since
  genus preservation is precisely the hypothesis `lemma-dangling-limit` runs on,
  this says the assumption behind `hReflected` below and the derived Equation (C)
  are two readings of the same single unit of correction.
* `endpoints_trivalent_of_fourStar` — the converse bookkeeping: a `FourStar` at
  the merged vertex forces `val(u) = val(v) = 3` and `ch(u) = ch(v) = 0`.  So the
  four-valent wall is exactly what one gets by contracting an occurrence between
  two change-free trivalent target vertices, and the hypotheses of the main
  theorem pin each other down rather than floating free.
* `fourStarMerge` — conversely, `val(u) + val(v) = 6` produces the star.
* `auxR0SourceInput_of_contraction` — the main theorem.
* `not_nonempty_labelling_contractDatum` — the wall datum admits no square
  honest stable labelling of its own.  This is why no contradiction arises: the
  two data are genuinely different data.

Assumed, and named as hypotheses of the main theorem rather than fields of a
structure so that every consumer sees them:

* `hForest : ContractionRamification.ContractionForest data a b contracted` —
  Draisma–Vargas's source-topology receipt for the contracted occurrence.  It
  is produced from a terminal face's census by
  `ZeroForestBridge.contractionForest_of_isForest_of_targetLength_eq_zero`; it is
  not invented here.
* `hReflected : WallDegeneration.DanglingReflected data hc hab hOne` — **assumed,
  not derived.**  As `WallDegeneration`'s docstring explains, the statement fails
  without a hypothesis: contracting can create dangling occurrences when the
  contracted source fibre carries a cycle.  The hypothesis that rescues it is
  genus preservation, which Part I states as `lemma-dangling-limit` ("dangling
  in the limit": if `g(H(M)) = g(H(M₀))` then a vertex above `w₀` is dangling if
  and only if all the vertices contracting to it are), and which in this
  development is exactly `ContractionForest` -- the paper derives forest-ness of
  the contracted fibre from genus preservation.  So `hReflected` is carried
  *alongside* `hForest`, never instead of it, and nothing here assumes the
  unconditional form.  Deriving it would need connectivity and genus bookkeeping
  for `Utilities.inducedSubgraph` under contraction, which is not developed
  here; it is carried as a hypothesis instead.
* `hStable : Nonempty (StablePath (contractDatum …) ≃ StablePath data)` — the
  paper's claim that the stable model `H(M)` survives the degeneration.  It is
  `WallDegeneration.stablePath`, unchanged.
* `hTrivalent` — trivalence of the *wall* datum's stable graph at the wall
  blocks.  This is the same input as `FullDimensionalSourcePresentation.trivalent`
  read on the other datum, and it does **not** follow from it: the merged source
  vertex accumulates the surviving occurrences of every source vertex in its
  fibre, so `nd ≤ 3` upstairs bounds `nd` downstairs only by `6`.  It is the
  wall-datum half of "`H(M)` survives", exactly as `hStable` is.

## Why the hypotheses are compatible

The following reading explains why the hypotheses do not contradict one
another.  It does not exhibit an instance; see *The numerology* below.

*The two data are different data, by design.*  `fullDim` is a presentation of
`data`; the conclusion is an interface for `contractDatum data …`.  The two
`FullDimensionalSource` inconsistencies are inconsistencies *within one datum*:
`equation_c` versus `ChangeMinimal`, and `stablePath_card` versus a square
labelling.  Here `ChangeMinimal` and the square labelling are asserted of `data`
only, while `equation_c` and `stablePath_card` are asserted of
`contractDatum data …` only.  `targetExcess_contractDatum_merge_eq_one` is the
proof that the first pair is not merely unrelated but *equivalent*: the wall's
excess is `1` **because** the full-dimensional datum's excess is `0` at both
ends.  `not_nonempty_labelling_contractDatum` is the proof that the second pair
is consistent: the wall datum provably has no square labelling of its own, so no
declaration can turn `stablePath_card` into a contradiction.

*The numerology.*  `fullDim.changeMinimal` and `targetChange_nonneg` give
`val(w) ≤ 3` at every target vertex of `data`, and `endpoints_trivalent_of_fourStar`
forces `val(u) = val(v) = 3`, `ch(u) = ch(v) = 0` at the two contracted
endpoints.  So the target of `data` is a genus-zero connected graph -- a tree --
whose contracted edge joins two trivalent vertices; contracting it produces the
four-valent wall.  With `t` target edges, `fullDim.stablePath_card` gives
`#StablePath data = t` and `hStable` gives `#StablePath (contractDatum …) = t =
(t - 1) + 1`, which is the wall count on the nose.

The size of `t` is constrained further.
`TrivalenceClosure.card_target_edges_eq_of_presentation` gives

```
(target.edges.card : ℤ) = 3 * genus data.sourceGraph - 3 * stableComponentCount data
```

for *every* `FullDimensionalSourcePresentation`, so `3 ∣ t`.  With
`genus_sourceGraph_eq_of_presentation` this sharpens to
`t = 6 (degree + c(H)) - 15`, i.e. `t ∈ {3, 9, 15, …}`.  A four-star at the merged
vertex needs four occurrences in the contracted target, so `t - 1 ≥ 4`; the least
admissible value is therefore `9`, forcing `degree ≥ 3` and `genus(source) ≥ 4`.
The smallest shape consistent with the constraints is `t = 9`, `degree = 3`,
`c(H) = 1`, `genus(source) = 4`, with stable graph `K_{3,3}`.  (In particular the
six-vertex tree with two adjacent trivalent vertices and four leaves, `t = 5`,
is not a target of this situation.)  That shape is arithmetically admissible,
so the counting does not make the bundle vacuous; but this module exhibits no
instance, and the joint satisfiability of the hypotheses is not established
here.  The qualitative readings -- why the two data are genuinely different
data, and why `hForest`, `hReflected`, `hTrivalent` and `hStable` describe one
picture rather than four -- do not depend on the value of `t`.

*`hForest`, `hReflected`, `hTrivalent` and `hStable` describe one picture, not
four.*  Take the contracted occurrence unramified: every block above `u`, above
`v` and above the occurrence a singleton.  Then the merged partition is the join
of two discrete partitions, every merged block carries `p = q = E = 1`, and
`hForest` reads `1 + 1 = 1 + 1`.  The single source occurrence `e` above the
contracted target occurrence in each merged block is then either dangling or
surviving, and `hTrivalent` at that block reads
`nd(u_i) + nd(v_i) - 2·[e surviving] ≤ 3`.  By `fullDim`'s trichotomy each of
`nd(u_i), nd(v_i)` is `0`, `2` or `3`, so the surviving case is satisfied exactly
when at least one end has `nd = 2` -- that is, when `e` lies in the *interior* of
a stable path rather than joining two vertices of `H(M)`.  That is also precisely
the configuration in which contracting `e` leaves the stable-path classes in
bijection, which is `hStable`, and in which no cycle is contracted, which is what
`lemma-dangling-limit` needs for `hReflected`.  The four hypotheses are the same
statement about one degeneration, read four ways; they constrain each other but
do not contradict each other.  `genus_sourceGraph_contractDatum_eq` is the part
of that reading which is a theorem rather than prose: the genus condition behind
`hReflected` holds exactly when the wall datum spends its whole unit of dimension
correction at the wall, which is what `equation_c` says it does.

*What would make the bundle vacuous, and does not happen here.*  It would be
vacuous if some declaration forced `#StablePath (contractDatum …) ≤
(contract target).edges.card`, or forced the wall datum to be change-minimal.
The first needs a square labelling of the wall datum, refuted by
`not_nonempty_labelling_contractDatum`; the second is refuted by
`targetExcess_contractDatum_merge_eq_one`, which *derives* excess `1`.  Neither
is available, and neither is assumed.
-/

namespace DraismaVargas.LocalCases.W4Bridge

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.NonDanglingValency
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.WallDegeneration

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-! ## Two pieces of block bookkeeping -/

/-- Summing over the fine blocks inside each coarse block, coarse block by
coarse block, is summing over all fine blocks. -/
private theorem sum_blocksWithin_eq {size : ℕ} (fine coarse : SheetPartition size)
    (value : fine.Blocks → ℤ) :
    (∑ coarseBlock : coarse.Blocks,
        ∑ fineBlock ∈ SheetPartition.blocksWithin fine coarse coarseBlock,
          value fineBlock)
      = ∑ fineBlock : fine.Blocks, value fineBlock := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset fine.Blocks))
    (t := (Finset.univ : Finset coarse.Blocks))
    (g := SheetPartition.fineBlockToCoarseBlock fine coarse)
    (fun fineBlock _ ↦ Finset.mem_univ _) value]
  refine Finset.sum_congr rfl fun coarseBlock _ ↦ Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext fineBlock
  simp

/-- Equal sheet partitions have the same blocks to sum over. -/
private theorem sum_blocks_congr {size : ℕ} {first second : SheetPartition size}
    (hEq : first = second) (value : Fin size → ℤ) :
    (∑ block : first.Blocks, value block.1)
      = ∑ block : second.Blocks, value block.1 := by
  subst hEq
  rfl

/-! ## The change at the merged vertex -/

/-- **Draisma–Vargas Part I, `prop-rphi-under-contraction`, second conclusion:
`ch(w₀) = ch(u) + ch(v)`.**

`ContractionRamification.localRamificationAt_contractDatum_merge` proves the
additivity one merged block at a time.  Summing it over the blocks of the merged
partition is all that is left, because the blocks of the two endpoint partitions
inside the merged blocks exhaust those partitions
(`sum_blocksWithin_eq`). -/
theorem targetChange_contractDatum_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted) :
    (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩
      = data.targetChange a + data.targetChange b := by
  classical
  calc (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩
      = ∑ block : ((contractDatum data hc hab hOne).vertexPartition
              ⟨a, hab⟩).Blocks,
          localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 :=
        rfl
    _ = ∑ block : (mergedPartition data a b).Blocks,
          localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 :=
        sum_blocks_congr (contractDatum_vertexPartition_merge data hc hab hOne) _
    _ = ∑ block : (mergedPartition data a b).Blocks,
          ((∑ fibreBlock ∈ SheetPartition.blocksWithin (data.vertexPartition a)
                (mergedPartition data a b) block,
              data.localRamification a fibreBlock)
            + ∑ fibreBlock ∈ SheetPartition.blocksWithin (data.vertexPartition b)
                (mergedPartition data a b) block,
              data.localRamification b fibreBlock) :=
        Finset.sum_congr rfl fun block _ ↦
          localRamificationAt_contractDatum_merge data hc hab hOne hForest block
    _ = data.targetChange a + data.targetChange b := by
        rw [Finset.sum_add_distrib,
          sum_blocksWithin_eq (data.vertexPartition a) (mergedPartition data a b)
            (data.localRamification a),
          sum_blocksWithin_eq (data.vertexPartition b) (mergedPartition data a b)
            (data.localRamification b)]
        rfl

/-- The excess at the merged vertex.  The change adds
(`targetChange_contractDatum_merge`) and the valency adds after losing the two
ends of the contracted occurrence (`card_incidentEdges_merge`), so one unit of
excess is created. -/
theorem targetExcess_contractDatum_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted) :
    (contractDatum data hc hab hOne).targetExcess ⟨a, hab⟩
      = data.targetExcess a + data.targetExcess b + 1 := by
  have hChange := targetChange_contractDatum_merge data hc hab hOne hForest
  have hValency : ((GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card : ℤ)
      + 2 = ((GluingDatum.incidentEdges a).card : ℤ)
        + ((GluingDatum.incidentEdges b).card : ℤ) := by
    exact_mod_cast congrArg (fun count : ℕ ↦ (count : ℤ))
      (card_incidentEdges_merge hc hab hOne)
  show (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩
      + ((GluingDatum.incidentEdges
        (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card : ℤ)
      - 3 = _
  rw [hChange]
  show _ = (data.targetChange a + ((GluingDatum.incidentEdges a).card : ℤ) - 3)
      + (data.targetChange b + ((GluingDatum.incidentEdges b).card : ℤ) - 3) + 1
  linarith

/-- **Equation (C) is derived, not assumed.**  The full-dimensional datum is
change-minimal, so its excess vanishes at both ends of the contracted
occurrence; the contraction creates exactly one unit of excess at the merged
vertex, which is the `equation_c` field of `W4StableSource.AuxR0SourceInput`. -/
theorem targetExcess_contractDatum_merge_eq_one (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (hMinimal : data.ChangeMinimal) :
    (contractDatum data hc hab hOne).targetExcess ⟨a, hab⟩ = 1 := by
  have hLeft : data.targetExcess a = 0 := hMinimal a
  have hRight : data.targetExcess b = 0 := hMinimal b
  rw [targetExcess_contractDatum_merge data hc hab hOne hForest, hLeft, hRight]
  ring

/-! ## The global cross-check: where the wall's unit of excess comes from -/

/-- **The wall datum's total dimension correction.**  Contraction keeps the
target genus zero (`GraphContraction.genus_contract`) and drops one target edge,
so the dimension-correction identity read on the contracted datum, against the
saturation of the datum it comes from, says the whole correction of the wall
datum is `1` plus twice the source genus the contraction created.

Nothing about the contraction's source topology is used here, so this is a free
cross-check on the interface: the wall datum is exactly one step off saturation,
which is what "codimension one" means. -/
theorem sum_targetExcess_contractDatum {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    (∑ vertex : (GraphContraction.contract target hab hOne).V,
        (contractDatum data hc hab hOne).targetExcess vertex)
      = 2 * genus (contractDatum data hc hab hOne).sourceGraph
        - 2 * genus data.sourceGraph + 1 := by
  have hGenus : genus (GraphContraction.contract target hab hOne) = 0 := by
    rw [GraphContraction.genus_contract]
    exact fullDim.targetGenus
  have hDim := (contractDatum data hc hab hOne).dimensionCorrection_of_target_genus_zero
    hGenus
  have hEdge : (target.edges.card : ℤ)
      = ((GraphContraction.contract target hab hOne).edges.card : ℤ) + 1 := by
    exact_mod_cast congrArg (fun count : ℕ ↦ (count : ℤ)) (edge_card_contract hab hOne)
  have hSaturated := fullDim.saturated
  linarith

/-- **Genus preservation and Equation (C) are the same unit of correction.**  If
the wall datum is change-minimal at every target vertex other than the merged
one, then the contraction preserves the source genus: the single unit of
dimension correction that `targetExcess_contractDatum_merge_eq_one` places at the
wall is the *whole* correction, leaving none to be spent on source genus.

This is the coherence receipt for the hypothesis bundle of
`auxR0SourceInput_of_contraction`.  Source-genus preservation is exactly the
condition Draisma–Vargas Part I's `lemma-dangling-limit` runs on, and hence the
justification for assuming `WallDegeneration.DanglingReflected`; the theorem says
that condition is not an extra wish layered on top of Equation (C) but the same
arithmetic read the other way. -/
theorem genus_sourceGraph_contractDatum_eq {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hAway : ∀ vertex : (GraphContraction.contract target hab hOne).V,
      vertex ≠ ⟨a, hab⟩ →
        (contractDatum data hc hab hOne).targetExcess vertex = 0) :
    genus (contractDatum data hc hab hOne).sourceGraph
      = genus data.sourceGraph := by
  classical
  have hSum := sum_targetExcess_contractDatum data hc hab hOne fullDim
  have hWall := targetExcess_contractDatum_merge_eq_one data hc hab hOne hForest
    fullDim.changeMinimal
  have hSplit : (∑ vertex : (GraphContraction.contract target hab hOne).V,
        (contractDatum data hc hab hOne).targetExcess vertex)
      = (contractDatum data hc hab hOne).targetExcess ⟨a, hab⟩ :=
    Finset.sum_eq_single _ (fun vertex _ hNe ↦ hAway vertex hNe)
      (fun hNot ↦ absurd (Finset.mem_univ _) hNot)
  rw [hSplit, hWall] at hSum
  linarith

/-! ## The four-valent wall, and what it forces upstairs -/

/-- A four-star is exactly a four-valent vertex. -/
theorem card_incidentEdges_of_fourStar {wallTarget : CFGraph} {wall : wallTarget.V}
    (star : W4TargetPairings.FourStar wallTarget wall) :
    (GluingDatum.incidentEdges wall).card = 4 := by
  classical
  have hCard := Fintype.card_congr star.label
  simpa using hCard.symm

/-- Contracting an occurrence between two trivalent target vertices produces the
four-valent W4 wall. -/
noncomputable def fourStarMerge (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (hCard : (GluingDatum.incidentEdges a).card
      + (GluingDatum.incidentEdges b).card = 6) :
    W4TargetPairings.FourStar (GraphContraction.contract target hab hOne)
      ⟨a, hab⟩ :=
  W4TargetPairings.FourStar.of_card (by
    have hMerge := card_incidentEdges_merge hc hab hOne
    omega)

/-- **The hypotheses pin each other down.**  If the merged vertex carries a
four-star and the datum being contracted is valid and change-minimal, then the
two contracted endpoints are trivalent and change-free.  So the main theorem
below is not a bundle of free parameters: the shape of the target at the
contracted occurrence is forced by the wall it is asked to produce. -/
theorem endpoints_trivalent_of_fourStar (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hMinimal : data.ChangeMinimal)
    (star : W4TargetPairings.FourStar (GraphContraction.contract target hab hOne)
      ⟨a, hab⟩) :
    (GluingDatum.incidentEdges a).card = 3 ∧
      (GluingDatum.incidentEdges b).card = 3 ∧
        data.targetChange a = 0 ∧ data.targetChange b = 0 := by
  have hStar := card_incidentEdges_of_fourStar star
  have hMerge := card_incidentEdges_merge hc hab hOne
  have hLeftLe := GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt data
    hValid a (hMinimal a)
  have hRightLe := GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt data
    hValid b (hMinimal b)
  have hLeftCard : (GluingDatum.incidentEdges a).card = 3 := by omega
  have hRightCard : (GluingDatum.incidentEdges b).card = 3 := by omega
  have hLeftExcess : data.targetChange a
      + ((GluingDatum.incidentEdges a).card : ℤ) - 3 = 0 := hMinimal a
  have hRightExcess : data.targetChange b
      + ((GluingDatum.incidentEdges b).card : ℤ) - 3 = 0 := hMinimal b
  rw [hLeftCard] at hLeftExcess
  rw [hRightCard] at hRightExcess
  push_cast at hLeftExcess hRightExcess
  refine ⟨hLeftCard, hRightCard, by linarith, by linarith⟩

/-! ## The W4 wall interface, fed from the degeneration -/

/-- **The main theorem.**  A full-dimensional presentation of `data`, together
with the contraction receipts, feeds `W4StableSource.AuxR0SourceInput` for the
*contracted* datum at the merged vertex.

Field by field:

* `valid` is `ContractionRamification.valid_contractDatum` from `fullDim.valid`
  and `hForest`;
* `stablePath_card` is `WallDegeneration.stablePath_card_contractDatum`, whose
  stable-path equivalence is `hStable`;
* `dangling_no_glue` is `WallDegeneration.danglingEdgeNoGlue_contractDatum`,
  which consumes `hReflected` -- the direction that fails unconditionally and
  holds under the genus-preservation hypothesis carried here as `hForest`;
* `nonDangling_valency` is the trichotomy, from connectedness of the contracted
  datum and `hTrivalent`;
* `equation_c` is `targetExcess_contractDatum_merge_eq_one`: **proved**, from
  `fullDim.changeMinimal` and `hForest`. -/
theorem auxR0SourceInput_of_contraction {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {star : W4TargetPairings.FourStar (GraphContraction.contract target hab hOne)
      ⟨a, hab⟩}
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hForest : ContractionForest data a b contracted)
    (hStable : Nonempty
      (StablePath (contractDatum data hc hab hOne) ≃ StablePath data))
    (hReflected : DanglingReflected data hc hab hOne)
    (hTrivalent : ∀ sourceBlock : WallBlock (contractDatum data hc hab hOne)
        ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
            sourceBlock) ≤ 3) :
    AuxR0SourceInput (contractDatum data hc hab hOne) star where
  valid := valid_contractDatum data hc hab hOne hForest fullDim.valid
  stablePath_card :=
    stablePath_card_contractDatum data hc hab hOne fullDim hStable
  dangling_no_glue :=
    danglingEdgeNoGlue_contractDatum data hReflected fullDim.danglingEdgeNoGlue
  nonDangling_valency :=
    wallBlock_nonDanglingValency_eq_zero_or_two_or_three
      (contractDatum data hc hab hOne)
      (valid_contractDatum data hc hab hOne hForest fullDim.valid) hTrivalent
  equation_c :=
    targetExcess_contractDatum_merge_eq_one data hc hab hOne hForest
      fullDim.changeMinimal

/-- **Why the bundle above is not self-contradictory.**  The wall datum admits
no square honest stable length-matrix labelling of its own, for any coordinate
type, so `stablePath_card` above cannot be turned against it the way
`FullDimensionalSource.stablePath_card_ne_succ` turns it against a
full-dimensional datum.  This is
`WallDegeneration.not_nonempty_labelling_of_wallDegeneration` read on the
contraction. -/
theorem not_nonempty_labelling_contractDatum {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate] {wallCoordinate : Type*}
    [Fintype wallCoordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hStable : Nonempty
      (StablePath (contractDatum data hc hab hOne) ≃ StablePath data)) :
    ¬ Nonempty (StableLengthMatrixLabelling (contractDatum data hc hab hOne)
      wallCoordinate) :=
  not_nonempty_labelling_of_wallDegeneration fullDim
    (wallDegeneration_contractDatum data hc hab hOne hStable)

end DraismaVargas.LocalCases.W4Bridge
