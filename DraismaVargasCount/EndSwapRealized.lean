module

public import DraismaVargasCount.CatFlipRealizedAut

@[expose] public section

/-!
# The end swap is realised by the caterpillar gluing datum, at every even genus

At every even genus at least four the caterpillar core `FibreCaterpillar.catCore (m + 1)` has a
core symmetry that is not the genus-two reflection: the exchange `SlopeRigidity.endSwap m` of the
two loops hanging at the near end of the spine (`CatFlipRealizedAut`).  It stabilises the ballot
core diagonal of *every* slope sequence with no hypothesis
(`SlopeRigidity.endSwap_stabilises_ballotCoreDiag`).  This module shows that it is realised by
the caterpillar member, for every `m` and every request: `realizes_endSwap`.  So the route to a
refutation of `rigid` through the end swap (`not_coreDiagRigid_of_not_realizes_endSwap`) never
applies.  `realizes_endSwap` is used in `DiagonalClassificationGenusSix`.

## The sheet layer

At genus two the vertex partition `catVertexPart 0` is the *constant* partition `pairPart 0 1`,
so the sheet layer of a datum isomorphism is free.  That is special to genus two:
`catVertexPart M v = pairPart M (pairIndex v.val)` and `pairIndex` is the *pair* index
`(lolli v + 1) / 2`, which takes every value in `{1, …, M + 1}`.  `catVertexPart_not_constant`
records this in Lean, at every `M ≥ 1`.

What survives is weaker and is exactly what the sheet layer needs: the end swap moves no vertex
out of its pair.  It is supported on the target vertices `u₁ = 0`, `v₁ = 1`, `u₂ = 3`, `v₂ = 4`,
and all four lie in lollipops `1` and `2`, which form pair `1`.  So `pairIndex` is preserved
(`pairIndex_endSwapTgt`), hence so is the vertex partition, and the identity sheet permutations
still discharge `vertexPartition`, `edgePartition` and `compatible`.  `endSwapSheetIso` is the
resulting builder: it asks for *preservation* of the two partitions, where the genus-two
construction can use constancy of one of them.

## How the rest is built

The target automorphism is the involution `endSwapTgtFun m` of `catTree (m+1)` exchanging
`0 ↔ 3` and `1 ↔ 4` and fixing every other vertex -- the lift of `endSwap m`, whose slot part
`(0 3)(1 2)` it induces through the occurrence dictionary `catEdgeEquiv (m+1)`.  Unordered
endpoints are a five-case check (the four moved occurrences, and everything from index four up,
where both endpoints are fixed because `parentIndex v ∉ {0, 1, 3, 4}` for `v ≥ 5`).

The two `overCore` equations are then the same computations as at genus two: `rowIndex` is
`Quot.lift` of "the target occurrence beneath the source edge", so the row equation is
`endSwapSlotFun ∘ endSwapSlotFun = id`; and `branchIndexOf` reads `branchIdx` of the target
vertex, so the vertex equation is `branchIdx` of the four moved vertices against the core
involution `(0 2)`, with the two folded tips `1`, `4` excluded because they are not branch
indices.

## Main results

* `catVertexPart_not_constant` -- the vertex partition of `caterpillarDatum M` really does vary,
  at every `M ≥ 1`.
* `endSwapTgtFun`, `endSwapTgtEquiv`, `endSwapEdgeEquiv`, `endSwap_ends` -- the target
  automorphism lifting `endSwap m`, with its unordered-endpoint receipt.
* `pairIndex_endSwapTgt`, `endSwap_vertexPart`, `endSwap_edgePart` -- both occurrence partitions
  are preserved.
* `endSwapSheetIso` -- the sheet layer, discharged for *any* target automorphism preserving the
  two partitions, with identity sheet permutations.  It is reused by `BallotEndSwapSheetIso` and
  `BallotFarEndSwap`.
* `endSwapDatumIso` -- **the self-isomorphism of `caterpillarDatum (m+1)`.**
* `endSwapDatumIso_overCore_row`, `endSwapDatumIso_overCore_vertex` -- the two equations
  `SlopeRigidity.Realizes` asks for.
* **`realizes_endSwap`** -- `Realizes (endSwap m) (caterpillarMember (m+1) request)` for every
  `m` and every request whatsoever.
* `cls_caterpillarEndTwist_eq` -- the consequence for the end twist
  `SlopeRigidity.caterpillarEndTwist`: the caterpillar member and its end twist are the *same*
  geometric class, so the pair of distinct members exhibited by `SlopeRigidity.generic_witness`
  is not a pair of classes.
* `not_realizes_endSwap_elim` -- no member refutes `rigid` through `endSwap` at the caterpillar.

## Remarks

* This file realises one symmetry on one member.  Residue (B) of `rigid`
  (`SlopeRigidity.DiagonalSymmetryRealized`) quantifies over every open odd member whose core
  diagonal is stabilised, and over every stabilising symmetry of it.
* `hconn` is always `(caterpillarMember (m+1) request).fullDim.valid.1`; no positivity,
  genericity or integrality of the request is used anywhere.
-/

namespace DraismaVargas.Count.SlopeRigidity

open DraismaVargas.Count
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.W4StableSource
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  The genus-two shortcut is a genus-two accident -/

/-- **The vertex partition of `caterpillarDatum M` is not constant for `M ≥ 1`.**
At `M = 0`, `catVertexPart 0` is the constant `pairPart 0 1`, which is what
makes the genus-two sheet layer free.  The reason
is that at `M = 0` the two lollipops `1`, `2` are the only ones and they form a
single pair; as soon as `M ≥ 1` the last lollipop belongs to pair `M + 1`.  So a
higher-genus construction has to *preserve* the vertex partition, not ignore
it. -/
theorem catVertexPart_not_constant (m : ℕ) :
    catVertexPart (m + 1) (vtx (m + 1) 0 (by omega)) ≠
      catVertexPart (m + 1) (vtx (m + 1) (6 * (m + 1) + 3) (by omega)) := by
  have hlt1 : 1 < m + 1 + 2 := by omega
  have h0 : catVertexPart (m + 1) (vtx (m + 1) 0 (by omega)) = pairPart (m + 1) 1 := by
    rw [catVertexPart_val (m + 1) _ 0 rfl]
    congr 1
  have h1 : catVertexPart (m + 1) (vtx (m + 1) (6 * (m + 1) + 3) (by omega))
      = pairPart (m + 1) (m + 2) := by
    rw [catVertexPart_val (m + 1) _ (6 * (m + 1) + 3) rfl]
    congr 1
    all_goals (unfold pairIndex lolli; omega)
  rw [h0, h1]
  intro h
  have hfix : (pairPart (m + 1) (m + 2)).repr ⟨1, hlt1⟩ = ⟨1, hlt1⟩ :=
    (pairPart_fixed_iff (m + 1) (m + 2) (by omega) ⟨1, hlt1⟩).mpr
      (show (1 : ℕ) ≠ m + 2 by omega)
  rw [← h] at hfix
  exact (pairPart_fixed_iff (m + 1) 1 le_rfl ⟨1, hlt1⟩).mp hfix rfl

/-! ## 2.  The target automorphism lifting the end swap -/

/-- The involution of `catTree (m+1)` underlying the end swap: `u₁ ↔ u₂` and
`v₁ ↔ v₂`, i.e. `0 ↔ 3` and `1 ↔ 4`, with every other target vertex fixed. -/
def endSwapTgtFun (m : ℕ) (v : (catTree (m + 1)).V) : (catTree (m + 1)).V :=
  ⟨(if v.val = 0 then 3 else if v.val = 1 then 4 else if v.val = 3 then 0
      else if v.val = 4 then 1 else v.val), by have := v.isLt; split_ifs <;> omega⟩

theorem endSwapTgtFun_val (m : ℕ) (v : (catTree (m + 1)).V) :
    (endSwapTgtFun m v).val =
      if v.val = 0 then 3 else if v.val = 1 then 4 else if v.val = 3 then 0
        else if v.val = 4 then 1 else v.val := rfl

/-- Away from the four moved vertices the involution is the identity. -/
theorem endSwapTgtFun_fix (m : ℕ) (v : (catTree (m + 1)).V)
    (h0 : v.val ≠ 0) (h1 : v.val ≠ 1) (h3 : v.val ≠ 3) (h4 : v.val ≠ 4) :
    endSwapTgtFun m v = v := by
  apply Fin.ext
  rw [endSwapTgtFun_val, ite_eq_right h0, ite_eq_right h1, ite_eq_right h3, ite_eq_right h4]

theorem endSwapTgtFun_involutive (m : ℕ) : Function.Involutive (endSwapTgtFun m) := by
  intro v
  apply Fin.ext
  rw [endSwapTgtFun_val, endSwapTgtFun_val]
  split_ifs <;> first | contradiction | omega

/-- The involution, as a permutation of the target vertices. -/
def endSwapTgtEquiv (m : ℕ) : (catTree (m + 1)).V ≃ (catTree (m + 1)).V :=
  (endSwapTgtFun_involutive m).toPerm _

@[simp] theorem endSwapTgtEquiv_apply (m : ℕ) (v : (catTree (m + 1)).V) :
    endSwapTgtEquiv m v = endSwapTgtFun m v := rfl

/-- **The parent of a target vertex of index at least five is never one of the
four moved vertices.**  This is what makes the end swap supported at one end of
the spine at the level of the *tree*, not merely of the core. -/
theorem parentIndex_not_moved {v : ℕ} (h : 5 ≤ v) :
    parentIndex v ≠ 0 ∧ parentIndex v ≠ 1 ∧ parentIndex v ≠ 3 ∧ parentIndex v ≠ 4 := by
  unfold parentIndex
  split_ifs <;> omega

/-- The tail of the target occurrence `i`, at the level of indices. -/
theorem occ_fst_val (M : ℕ) (i : Fin (6 * M + 3)) :
    ((occ M i : (catTree M).edges) : (catTree M).V × (catTree M).V).1.val
      = parentIndex (i.val + 1) := rfl

/-- The head of the target occurrence `i`, at the level of indices. -/
theorem occ_snd_val (M : ℕ) (i : Fin (6 * M + 3)) :
    ((occ M i : (catTree M).edges) : (catTree M).V × (catTree M).V).2.val = i.val + 1 := rfl

/-- The slot part of the end swap, at the level of indices. -/
theorem endSwap_slot_val (m : ℕ) (e : Fin (6 * (m + 1) + 3)) :
    ((endSwap m).slot e).val =
      if e.val = 0 then 3 else if e.val = 1 then 2 else if e.val = 2 then 1
        else if e.val = 3 then 0 else e.val := by
  rw [endSwap_slot_apply, endSwapSlotFun_val]

/-! ## 3.  The occurrence bijection -/

/-- The end swap on target occurrences: `endSwap m`'s slot permutation, read
through the occurrence dictionary. -/
noncomputable def endSwapEdgeEquiv (m : ℕ) :
    (catTree (m + 1)).edges ≃ (catTree (m + 1)).edges :=
  (catEdgeEquiv (m + 1)).symm.trans ((endSwap m).slot.trans (catEdgeEquiv (m + 1)))

theorem endSwapEdgeEquiv_occ (m : ℕ) (i : Fin (6 * (m + 1) + 3)) :
    endSwapEdgeEquiv m (occ (m + 1) i) = occ (m + 1) ((endSwap m).slot i) := by
  show catEdgeEquiv (m + 1)
    ((endSwap m).slot ((catEdgeEquiv (m + 1)).symm (catEdgeEquiv (m + 1) i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem endSwapEdgeEquiv_symm_apply (m : ℕ) (e : (catTree (m + 1)).edges) :
    (catEdgeEquiv (m + 1)).symm (endSwapEdgeEquiv m e) =
      (endSwap m).slot ((catEdgeEquiv (m + 1)).symm e) := by
  show (catEdgeEquiv (m + 1)).symm
    (catEdgeEquiv (m + 1) ((endSwap m).slot ((catEdgeEquiv (m + 1)).symm e))) = _
  rw [Equiv.symm_apply_apply]

/-- **The end swap preserves unordered endpoints.**  Four moved occurrences --
the loop `u₁v₁`, the spine edge `u₁p₂`, the stem `p₂u₂` and the loop `u₂v₂` --
and everything of index at least four is fixed on the nose. -/
theorem endSwap_ends (m : ℕ) (edge : (catTree (m + 1)).edges) :
    UnorderedEnds (endSwapTgtEquiv m) (edge : (catTree (m + 1)).V × (catTree (m + 1)).V)
      (endSwapEdgeEquiv m edge : (catTree (m + 1)).V × (catTree (m + 1)).V) := by
  obtain ⟨i, rfl⟩ := occ_surj (m + 1) edge
  rw [endSwapEdgeEquiv_occ]
  have hlt := i.isLt
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ 4 ≤ i.val by omega)
    with h | h | h | h | h
  · refine Or.inl (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;>
      simp only [endSwapTgtEquiv_apply, endSwapTgtFun_val, occ_fst_val, occ_snd_val,
        endSwap_slot_val, h] <;>
      norm_num [parentIndex]
  · refine Or.inr (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;>
      simp only [endSwapTgtEquiv_apply, endSwapTgtFun_val, occ_fst_val, occ_snd_val,
        endSwap_slot_val, h] <;>
      norm_num [parentIndex]
  · refine Or.inr (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;>
      simp only [endSwapTgtEquiv_apply, endSwapTgtFun_val, occ_fst_val, occ_snd_val,
        endSwap_slot_val, h] <;>
      norm_num [parentIndex]
  · refine Or.inl (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;>
      simp only [endSwapTgtEquiv_apply, endSwapTgtFun_val, occ_fst_val, occ_snd_val,
        endSwap_slot_val, h] <;>
      norm_num [parentIndex]
  · rw [endSwap_slot_of_four_le m i h]
    have hp := parentIndex_not_moved (show 5 ≤ i.val + 1 by omega)
    refine Or.inl (Prod.ext ?_ ?_)
    · exact (endSwapTgtFun_fix m _ hp.1 hp.2.1 hp.2.2.1 hp.2.2.2).symm
    · refine (endSwapTgtFun_fix m _ ?_ ?_ ?_ ?_).symm <;>
        · rw [occ_snd_val]; omega

/-! ## 4.  Both partitions are preserved -/

/-- **The end swap moves no target vertex out of its lollipop pair.**  The four
moved vertices `0, 1, 3, 4` lie in lollipops `1` and `2`, which form pair `1`. -/
theorem pairIndex_endSwapTgt (m : ℕ) (v : (catTree (m + 1)).V) :
    pairIndex (endSwapTgtFun m v).val = pairIndex v.val := by
  rw [endSwapTgtFun_val]
  unfold pairIndex lolli
  split_ifs <;> omega

/-- **The vertex partition is preserved**, which is what replaces the genus-two
constancy of `catVertexPart`. -/
theorem endSwap_vertexPart (m : ℕ) (v : (catTree (m + 1)).V) :
    catVertexPart (m + 1) (endSwapTgtFun m v) = catVertexPart (m + 1) v := by
  unfold catVertexPart
  rw [pairIndex_endSwapTgt]

/-- **The occurrence partition is preserved.**  The two loops carry the discrete
partition and are exchanged; the first spine edge and the first stem are both
pair edges of pair `1` and are exchanged; everything else is fixed. -/
theorem endSwap_edgePart (m : ℕ) (edge : (catTree (m + 1)).edges) :
    catEdgePart (m + 1) (endSwapEdgeEquiv m edge) = catEdgePart (m + 1) edge := by
  obtain ⟨i, rfl⟩ := occ_surj (m + 1) edge
  rw [endSwapEdgeEquiv_occ]
  have hlt := i.isLt
  unfold catEdgePart
  rw [edgeIndex_occ, edgeIndex_occ]
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ 4 ≤ i.val by omega)
    with h | h | h | h | h
  · have hslot : ((endSwap m).slot i).val = 3 := by rw [endSwap_slot_val, ite_eq_left h]
    have hp1 : ¬ IsPairEdge (m + 1) 3 := by unfold IsPairEdge; omega
    have hp2 : ¬ IsPairEdge (m + 1) 0 := by unfold IsPairEdge; omega
    rw [hslot, h, ite_eq_right hp1, ite_eq_right hp2]
  · have hslot : ((endSwap m).slot i).val = 2 := by
      rw [endSwap_slot_val, ite_eq_right (by omega), ite_eq_left h]
    have hp1 : IsPairEdge (m + 1) 2 := by unfold IsPairEdge; omega
    have hp2 : IsPairEdge (m + 1) 1 := by unfold IsPairEdge; omega
    rw [hslot, h, ite_eq_left hp1, ite_eq_left hp2]
    congr 1
  · have hslot : ((endSwap m).slot i).val = 1 := by
      rw [endSwap_slot_val, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
    have hp1 : IsPairEdge (m + 1) 1 := by unfold IsPairEdge; omega
    have hp2 : IsPairEdge (m + 1) 2 := by unfold IsPairEdge; omega
    rw [hslot, h, ite_eq_left hp1, ite_eq_left hp2]
    congr 1
  · have hslot : ((endSwap m).slot i).val = 0 := by
      rw [endSwap_slot_val, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
    have hp1 : ¬ IsPairEdge (m + 1) 0 := by unfold IsPairEdge; omega
    have hp2 : ¬ IsPairEdge (m + 1) 3 := by unfold IsPairEdge; omega
    rw [hslot, h, ite_eq_right hp1, ite_eq_right hp2]
  · rw [endSwap_slot_of_four_le m i h]

/-! ## 5.  The sheet layer -/

/-- **The sheet layer, discharged for every genus.**  A target automorphism of
`catTree (m+1)` that preserves unordered endpoints and *both* occurrence
partitions already assembles a self-isomorphism of `caterpillarDatum (m+1)`,
with the identity sheet permutation at every vertex and every occurrence.  At
genus two the constancy of `catVertexPart 0` can be used instead of a
preservation hypothesis; above genus two it cannot
(`catVertexPart_not_constant`). -/
def endSwapSheetIso (m : ℕ)
    (tv : (catTree (m + 1)).V ≃ (catTree (m + 1)).V)
    (te : (catTree (m + 1)).edges ≃ (catTree (m + 1)).edges)
    (hends : ∀ edge : (catTree (m + 1)).edges,
      UnorderedEnds tv (edge : (catTree (m + 1)).V × (catTree (m + 1)).V)
        (te edge : (catTree (m + 1)).V × (catTree (m + 1)).V))
    (hvertex : ∀ v : (catTree (m + 1)).V, catVertexPart (m + 1) (tv v) = catVertexPart (m + 1) v)
    (hedge : ∀ edge : (catTree (m + 1)).edges,
      catEdgePart (m + 1) (te edge) = catEdgePart (m + 1) edge) :
    GeometricDatumIso (caterpillarDatum (m + 1)) (caterpillarDatum (m + 1)) where
  targetVertex := tv
  targetEdge := te
  ends := hends
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition vertex := by
    show catVertexPart (m + 1) (tv vertex) = (catVertexPart (m + 1) vertex).relabel (Equiv.refl _)
    rw [hvertex, Transport.DatumIso.relabel_refl]
  edgePartition edge := by
    show catEdgePart (m + 1) (te edge) = (catEdgePart (m + 1) edge).relabel (Equiv.refl _)
    rw [hedge, Transport.DatumIso.relabel_refl]
  compatible _ _ _ _ := rfl

/-- **The self-isomorphism of the caterpillar gluing datum induced by the end
swap**, at every even genus at least four. -/
noncomputable def endSwapDatumIso (m : ℕ) :
    GeometricDatumIso (caterpillarDatum (m + 1)) (caterpillarDatum (m + 1)) :=
  endSwapSheetIso m (endSwapTgtEquiv m) (endSwapEdgeEquiv m) (endSwap_ends m)
    (endSwap_vertexPart m) (endSwap_edgePart m)

@[simp] theorem endSwapDatumIso_targetVertex (m : ℕ) :
    (endSwapDatumIso m).targetVertex = endSwapTgtEquiv m := rfl

@[simp] theorem endSwapDatumIso_targetEdge (m : ℕ) :
    (endSwapDatumIso m).targetEdge = endSwapEdgeEquiv m := rfl

/-! ## 6.  The two `overCore` equations -/

/-- **The row dictionary moves by the slot part of the end swap.** -/
theorem endSwapDatumIso_rowIndex (m : ℕ) (hconn : (caterpillarDatum (m + 1)).Connected)
    (edge : NonDanglingEdge (caterpillarDatum (m + 1))) :
    CaterpillarRows.rowIndex (m + 1)
        ((endSwapDatumIso m).stablePathEquiv hconn edge.stablePath) =
      (endSwap m).slot (CaterpillarRows.rowIndex (m + 1) edge.stablePath) := by
  rw [GeometricDatumIso.stablePathEquiv_mk]
  show (catEdgeEquiv (m + 1)).symm (endSwapEdgeEquiv m edge.1.1.1) =
    (endSwap m).slot ((catEdgeEquiv (m + 1)).symm edge.1.1.1)
  exact endSwapEdgeEquiv_symm_apply m _

/-- **The row half of `Realizes`**, the end swap being an involution on slots. -/
theorem endSwapDatumIso_overCore_row (m : ℕ) (hconn : (caterpillarDatum (m + 1)).Connected)
    (path : StablePath (caterpillarDatum (m + 1))) :
    (endSwap m).slot
        (CaterpillarRows.rowEquiv (m + 1) ((endSwapDatumIso m).stablePathEquiv hconn path)) =
      CaterpillarRows.rowEquiv (m + 1) path := by
  induction path using Quot.inductionOn with
  | h edge =>
    show (endSwap m).slot (CaterpillarRows.rowIndex (m + 1)
        ((endSwapDatumIso m).stablePathEquiv hconn edge.stablePath)) =
      CaterpillarRows.rowIndex (m + 1) edge.stablePath
    rw [endSwapDatumIso_rowIndex m hconn edge]
    exact endSwapSlotFun_involutive m _

/-- The vertex half, as arithmetic in the raw indices: the core involution
`(0 2)` intertwines `branchIdx` with the target involution, at **every** target
index -- no branch hypothesis is needed.  The folded tips come along for free
because `branchIdx` identifies `v_i` with `u_i`: `branchIdx 1 = branchIdx 0 = 0`
and `branchIdx 4 = branchIdx 3 = 2`, so `1 ↔ 4` induces the same core
transposition `(0 2)` that `0 ↔ 3` does. -/
theorem endSwapVtx_branchIdx (v : ℕ) :
    (if branchIdx (if v = 0 then 3 else if v = 1 then 4 else if v = 3 then 0
        else if v = 4 then 1 else v) = 0 then 2
      else if branchIdx (if v = 0 then 3 else if v = 1 then 4 else if v = 3 then 0
        else if v = 4 then 1 else v) = 2 then 0
      else branchIdx (if v = 0 then 3 else if v = 1 then 4 else if v = 3 then 0
        else if v = 4 then 1 else v)) = branchIdx v := by
  unfold branchIdx
  split_ifs <;> first | contradiction | omega

/-- **The vertex half of `Realizes`.**  A branch vertex of
`caterpillarDatum (m+1)` sits over a target vertex, and `branchIdx` sends the
four moved target vertices `0, 1, 3, 4` to the two core vertices `0` and `2`,
which is exactly the vertex part `(0 2)` of the end swap.  No branch hypothesis
is used (`endSwapVtx_branchIdx`). -/
theorem endSwapDatumIso_overCore_vertex (m : ℕ)
    (hconn : (caterpillarDatum (m + 1)).Connected)
    (b : BranchVertex (caterpillarDatum (m + 1))) :
    (endSwap m).vtx (branchEquiv (m + 1) ((endSwapDatumIso m).branchVertexEquiv hconn b)) =
      branchEquiv (m + 1) b := by
  apply Fin.ext
  show (endSwapVtxFun m
      (branchEquiv (m + 1) ((endSwapDatumIso m).branchVertexEquiv hconn b))).val =
    branchIdx b.1.1.1.val
  rw [endSwapVtxFun_val,
    show (branchEquiv (m + 1) ((endSwapDatumIso m).branchVertexEquiv hconn b)).val =
      branchIdx (endSwapTgtFun m b.1.1.1).val from rfl,
    endSwapTgtFun_val]
  exact endSwapVtx_branchIdx b.1.1.1.val

/-! ## 7.  The obligation, discharged -/

/-- **The end swap is realised by the caterpillar gluing datum, at every even
genus at least four and over every request.**  This is the conclusion of
`realizes_endSwap_of_coreDiagRigid`, proved unconditionally: no positivity of
the request, no genericity, no slope sequence, and no classification hypothesis
is used. -/
theorem realizes_endSwap (m : ℕ) (request : Fin (6 * (m + 1) + 3) → ℚ) :
    Realizes (endSwap m) (caterpillarMember (m + 1) request) :=
  ⟨endSwapDatumIso m, endSwapDatumIso_overCore_vertex m _, endSwapDatumIso_overCore_row m _⟩

/-- **The caterpillar member and its end twist are the same geometric class.**
`generic_witness` exhibits two *distinct members* with the
same core diagonal at every even genus at least four, even at an injective
request; this says they are nonetheless identified in `GeometricFibre.cls`,
which is what `rigid` needs of them. -/
theorem cls_caterpillarEndTwist_eq (m : ℕ) (request : Fin (6 * (m + 1) + 3) → ℚ) :
    GeometricFibre.cls (caterpillarMember (m + 1) request) =
      GeometricFibre.cls (caterpillarEndTwist m request) :=
  (cls_twistMember_eq_iff (endSwap m) (caterpillarMember (m + 1) request)
    (diagonal_caterpillarMember (m + 1) request)).mpr (realizes_endSwap m request)

/-- **The contrapositive route through the end swap never applies.**
`not_coreDiagRigid_of_not_realizes_endSwap` would refute
`rigid` from a failure of `Realizes (endSwap m) (caterpillarMember (m+1) request)`;
there is no such failure. -/
theorem not_realizes_endSwap_elim (m : ℕ) (request : Fin (6 * (m + 1) + 3) → ℚ)
    (h : ¬ Realizes (endSwap m) (caterpillarMember (m + 1) request)) : False :=
  h (realizes_endSwap m request)

end DraismaVargas.Count.SlopeRigidity
