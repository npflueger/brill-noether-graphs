import DraismaVargas.LocalCases.CaterpillarPruning
import DraismaVargas.LocalCases.FullDimensionalSource

/-!
# The caterpillar index map, and the seed presentation from stable data

`LocalCases.CaterpillarDatum` builds the caterpillar gluing datum and proves it
valid, with source genus `g`; this file records the *index map* that the length
matrix is built from, and a constructor that turns four stable-data inputs into
the full-dimensional source presentation of the seed.  `CaterpillarRows.fullDim`
supplies those four inputs, and `CaterpillarSeed.uniformInitialState` uses the
result as the seed of the semantic march in every even genus.

## What is here

* `blockCard_pairPart` -- the block cardinalities of `pairPart m j`: `2` on the
  glued block `{0, j}` and `1` elsewhere.
* `sourceEdgeIndex_caterpillar` -- **the index map `m(e)`** of the caterpillar
  morphism, for every occurrence and every sheet: `2` exactly on the source
  block through `{0, j}` over a pair edge, `1` on everything else.  The entries
  of the stable length matrix are the sums of `1 / m(e)` over a stable path, so
  this is the numerical input of the `DiagonalPattern`: a spine row will see
  `1/2` or `1` on its own column, a bridge row `1/2`, and a loop row `1 + 1`
  over its folded leaf edge.
* `presentationOfStableData` -- **the constructor**.  It supplies four of the
  eight fields of `FullDimensionalSourcePresentation` for the caterpillar datum
  over the coordinate type `Fin (3g-3)` (`valid`, `targetConnected`,
  `targetGenus`, `saturated`) and takes the other four as arguments.  That the
  `def` elaborates *is* the check that those four are discharged in exactly the
  form the structure demands.

## The four stable-data inputs (supplied by `CaterpillarRows`)

1. `labelling : StableLengthMatrixLabelling (caterpillarDatum m) (Fin (6*m+3))`
   -- the honest stable labelling: `targetEdge := catEdgeEquiv m` is already
   available, so what is needed is `row : StablePath (caterpillarDatum m) ≃
   Fin (6*m+3)`, i.e. the **dangling census**.  Concretely: every singleton
   occurrence of sheet `j` outside the `j`-th pair region is `IsDangling` (two
   explicit `DanglingSide`s per sheet, left and right of the pair), the
   `4g - 3` remaining occurrences are not, and `Consecutive` holds only at the
   `g` folds, giving `3g - 3` stable-path classes.
2. `det_ne_zero` -- from `SeedDeterminant.DiagonalPattern` on the resulting
   presentation: every displayed block of a row lies over that row's own
   column (`liesOver`) and no row is empty (`pathNeNil`); then
   `DiagonalPattern.det_ne_zero`.
3. `trivalent : ∀ v, nonDanglingValency (caterpillarDatum m) v ≤ 3`.  Note that
   this is *not* a consequence of the total valency: the block `{0, j}` above a
   junction `p_i` carries **four** source occurrences -- the bridge, the
   slope-two spine edge, and both index-one blocks over the slope-one spine
   edge -- and it is the census of 1 that makes one of the latter dangling.
4. `pathEnds : HasPathEnds (caterpillarDatum m)` -- every stable-path class
   meets an `A_i` or a `B_i`.
-/

namespace DraismaVargas.LocalCases.CaterpillarStable

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource

/-! ## 1.  The index map `m(e)` -/

theorem blockCard_pairPart (m j : ℕ) (hj1 : 1 ≤ j) (hj2 : j < m + 2)
    (k : Fin (m + 2)) :
    (pairPart m j).blockCard k = if (k : ℕ) = 0 ∨ (k : ℕ) = j then 2 else 1 := by
  by_cases hk : (k : ℕ) = 0 ∨ (k : ℕ) = j
  · rw [if_pos hk]
    have hrel : (pairPart m j).Rel k 0 := by
      rcases hk with h | h
      · have hk0 : k = 0 := Fin.ext (by simpa using h)
        rw [hk0]
        exact rfl
      · exact pairPart_rel_zero m j k h
    rw [SheetPartition.blockCard, (pairPart m j).block_eq_of_rel hrel]
    exact blockCard_pairPart_zero m j hj1 hj2
  · rw [if_neg hk]
    have hblock : (pairPart m j).block k = {k} := by
      ext l
      rw [SheetPartition.mem_block_iff, SheetPartition.rel_iff, Finset.mem_singleton,
        pairPart_repr, pairPart_repr, if_neg (fun h => hk (Or.inr h))]
      by_cases hl : (l : ℕ) = j
      · rw [if_pos hl]
        constructor
        · intro h
          have hzero : (k : ℕ) = 0 := by simpa using congrArg Fin.val h
          exact absurd (Or.inl hzero) hk
        · intro h
          exact absurd (Or.inr (h ▸ hl)) hk
      · rw [if_neg hl]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [SheetPartition.blockCard, hblock, Finset.card_singleton]

/-- **The index map of the caterpillar morphism.**  The dilation index of the
source block through sheet `s` over the occurrence `i` is `2` when `i` is a
pair edge and `s` lies in its glued block `{0, j}`, and `1` otherwise:  index
`2` on the slope-two spine edges and on the `g - 2` bridges
(`m(e_b) = 2`, as in Lemma `lm:bridge-and-loop` of Vargas, Part II, arXiv:2609.09109), index `1`
everywhere else. -/
theorem sourceEdgeIndex_caterpillar (m : ℕ) (i : Fin (6 * m + 3))
    (s : Fin (m + 2)) :
    (caterpillarDatum m).sourceEdgeIndex
        ((caterpillarDatum m).sourceEdge (occ m i) s)
      = if IsPairEdge m i.val ∧
          ((s : ℕ) = 0 ∨ (s : ℕ) = pairIndex (i.val + 1)) then 2 else 1 := by
  have hi := i.isLt
  rw [GluingDatum.sourceEdgeIndex_sourceEdge]
  show (catEdgePart m (occ m i)).blockCard s = _
  by_cases h : IsPairEdge m i.val
  · rw [catEdgePart_of_pair m i h,
      blockCard_pairPart m _ (pairIndex_pos _)
        (pairIndex_lt m (i.val + 1) (by omega)) s]
    by_cases hs : (s : ℕ) = 0 ∨ (s : ℕ) = pairIndex (i.val + 1)
    · rw [if_pos hs, if_pos ⟨h, hs⟩]
    · rw [if_neg hs, if_neg (fun hh => hs hh.2)]
  · rw [catEdgePart_of_not_pair m i h, blockCard_discrete,
      if_neg (fun hh => h hh.1)]

/-! ## 2.  The seed presentation from stable data -/

/-- **Four of the eight fields of the seed presentation are discharged.**

Given the other four -- the honest stable labelling, its nonsingularity,
trivalence of the stable graph and the path-end condition -- the caterpillar
datum is a full-dimensional source presentation over the
coordinate type `Fin (3g - 3)`.  The four supplied are `valid` (`Valid`
uniformly in `g`), `targetConnected` and `targetGenus` (from `TreeFamily`), and
`saturated` (the Euler count `genus = g` turned into `3g-3 = 2g+2d-5`).

Its four explicit arguments are exactly the stable-data inputs listed in the
module header, which `CaterpillarRows` supplies. -/
def presentationOfStableData (m : ℕ)
    (labelling : StableLengthMatrixLabelling (caterpillarDatum m) (Fin (6 * m + 3)))
    (det_ne_zero : (GluingDatum.LengthMatrixPresentation.matrix
      labelling.presentation).det ≠ 0)
    (trivalent : ∀ vertex : (caterpillarDatum m).SourceVertex,
      nonDanglingValency (caterpillarDatum m) vertex ≤ 3)
    (pathEnds : HasPathEnds (caterpillarDatum m)) :
    FullDimensionalSourcePresentation (caterpillarDatum m) (Fin (6 * m + 3)) where
  valid := caterpillarDatum_valid m
  targetConnected := catTree_connected m
  targetGenus := catTree_genus m
  saturated := saturated_caterpillarDatum m
  labelling := labelling
  det_ne_zero := det_ne_zero
  trivalent := trivalent
  pathEnds := pathEnds

/-! ## 3.  Non-vacuity

The index map is a real function at `g = 2` and `g = 4`. -/

/-- `g = 2`: the spine edge `h₁` carries index two on both sheets (slope `2`). -/
example : (caterpillarDatum 0).sourceEdgeIndex
    ((caterpillarDatum 0).sourceEdge (occ 0 ⟨1, by omega⟩) 0) = 2 := by
  rw [sourceEdgeIndex_caterpillar]
  norm_num [IsPairEdge, pairIndex, lolli]

example : (caterpillarDatum 0).sourceEdgeIndex
    ((caterpillarDatum 0).sourceEdge (occ 0 ⟨1, by omega⟩) ⟨1, by omega⟩) = 2 := by
  rw [sourceEdgeIndex_caterpillar]
  norm_num [IsPairEdge, pairIndex, lolli]

/-- `g = 2`: the folded leaf edge `u₁v₁` carries index one on every sheet. -/
example : (caterpillarDatum 0).sourceEdgeIndex
    ((caterpillarDatum 0).sourceEdge (occ 0 ⟨0, by omega⟩) 0) = 1 := by
  rw [sourceEdgeIndex_caterpillar]
  norm_num [IsPairEdge, pairIndex, lolli]

/-- `g = 4`: the bridge `p₂u₂` carries index two on the spine sheet. -/
example : (caterpillarDatum 1).sourceEdgeIndex
    ((caterpillarDatum 1).sourceEdge (occ 1 ⟨2, by omega⟩) 0) = 2 := by
  rw [sourceEdgeIndex_caterpillar]
  norm_num [IsPairEdge, pairIndex, lolli]

/-- `g = 4`: sheet `2` is the partner of the second pair, so it is glued over
`h₃` (occurrence `7`) and carries index two there. -/
example : (caterpillarDatum 1).sourceEdgeIndex
    ((caterpillarDatum 1).sourceEdge (occ 1 ⟨7, by omega⟩) ⟨2, by omega⟩) = 2 := by
  rw [sourceEdgeIndex_caterpillar]
  norm_num [IsPairEdge, pairIndex, lolli]

/-- `g = 4`: sheet `1` is *not* glued over `h₃`, so its block there has index
one -- it is the start of sheet `1`'s dangling tree to the right. -/
example : (caterpillarDatum 1).sourceEdgeIndex
    ((caterpillarDatum 1).sourceEdge (occ 1 ⟨7, by omega⟩) ⟨1, by omega⟩) = 1 := by
  rw [sourceEdgeIndex_caterpillar]
  norm_num [IsPairEdge, pairIndex, lolli]

/-- The coordinate type has the `3g - 3` elements the march needs. -/
example : Fintype.card (Fin (6 * 0 + 3)) = 3 * 2 - 3 := by
  rw [Fintype.card_fin]

example : Fintype.card (Fin (6 * 1 + 3)) = 3 * 4 - 3 := by
  rw [Fintype.card_fin]

end DraismaVargas.LocalCases.CaterpillarStable
