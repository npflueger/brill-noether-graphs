module

public import DraismaVargasCount.BallotEndSwapSheetIso
public import DraismaVargasCount.CaterpillarAllMembers

@[expose] public section

/-!
# The near end swap at every even genus, and the base count over the caterpillar of loops

This module extends the base count of the genus-six Draisma--Vargas count to every even genus at
least six. Over the caterpillar of loops `catCore (m + 1)`, of genus `2m + 4`, at every `m ≥ 1`
and every positive request, every member of the fibre in degree `m + 3` lies in a ballot class
and has multiplicity one, and there are exactly `catalan (m + 2)` open classes (`card_open`).
This is the count over a chain of loops of A. Vargas, *Catalan-many tropical morphisms to trees;
Part II: A space and a count*, arXiv:2609.09109: Part II, the proposition that every morphism over
a chain of loops comes from a ballot sequence (`prop-divisors-on-chain`), and the proposition that
a slope sequence determines its morphism (`prop-caterpillar-ballot`).

**Credit.** Sections 1–9 follow `BallotEndSwapSheetIso`, the genus-six template, rewritten from
genus six (`m = 1` here) to every `m`. The construction, the sheet transposition and the order of
the argument are that module's. What changes is index arithmetic: `catTree 2`, `ballotDatum 2 s`,
`Fin (2 + 2)` and `SlopeRigidity.endSwap 1` become `catTree (m + 1)`, `ballotDatum (m + 1) s`,
`Fin (m + 1 + 2)` and `SlopeRigidity.endSwap m`, and a few `by decide` on concrete indices become
`by omega`. Its general lemmas `catStar_relabel_eq` and `swap_pairval_iff` are reused, not
copied.

## Why the argument does not depend on `m`

The end swap `SlopeRigidity.endSwap m` of `catCore (m + 1)` moves the target vertices
`u₁ = 0`, `v₁ = 1`, `u₂ = 3`, `v₂ = 4` and the occurrences `0, 1, 2, 3`, all at the near end of
the spine. The blocks over them are `PairMem s 1 = {0, cum s 1} = {0, 1}` (also the first spine
block, `Slopes.spineMem_one_iff_pairMem_one`), `PairMem s 2 = {0, cum s 2}`, and the discrete
partition on the two loops. None of these depends on `m`: `cum s 1 = 1` always, and the only
place `m` enters `EdgePred` is the far leaf index `6 (m + 1) + 2`, which is not near the moved
occurrences. So the transposition `(1, cum s 2)` on the moved vertices and occurrences, and the
identity elsewhere, is a self-isomorphism of `ballotDatum (m + 1) s` over the end swap, at every
`m` (`bEndSwapDatumIso`). The `compatible` field needs only that `1` and `cum s 2` lie in the
same block over the spine vertex `p₂`, which is again a statement about indices `1` and `2` of
the slope sequence.

## What this gives

With the near end swap realised at every `m` (`ballotRealizes_endSwap`), the four relabellings
of the identity branch of `hStab` are realised at every `m ≥ 1`, in the shape `catCore (m + 1)`:
the identity, the near end swap (here), the far end swap
(`BallotFarEndSwap.ballotRealizes_farSwap`, already stated at every `m`) and their product
(`ballotRealizes_nearFarSwap`, here). §10 assembles them:

* `identity_branch_realized` -- every relabelling in the identity branch is realised, the
  every-`m` form of `BallotFarEndSwap.identity_branch_realized_genusSix`;
* `hStab` -- the stabiliser input of `CaterpillarAllMembers.cls_eq_ballot_of_diagonal`, through
  `BallotSpineReversalSheetIso.hStab_of_identity`;
* `cls_eq_ballot`, `absMult_eq_one`, `diagonalClassification`, `card_open` -- the integer base
  count over `catCore (m + 1)` at every `m ≥ 1`: at a positive request there are exactly
  `catalan (m + 2)` open classes, each of multiplicity one. At `m = 1` these are
  `CaterpillarAllMembers.cls_eq_ballot_genusSix`, `absMult_eq_one_genusSix`,
  `diagonalClassification_genusSix` and `card_open_genusSix` (`C₃ = 5`); at `m = 2`, genus
  eight, the count is `C₄ = 14`.

`EvenGenusParity` turns this count into the parity of the open odd count over every connected
cubic core of every even genus at least six.

## Scope

* The hypothesis `1 ≤ m` (that is, genus at least six) enters only through the identity-branch
  lemmas of `BallotStabiliserReduction`, which take `2 ≤ m + 1`. The sheet isomorphism of
  §§1–9 holds at every `m`, including `m = 0`.
* The target layer (`endSwapTgtEquiv m`, `endSwapEdgeEquiv m`) is chosen, as in
  `BallotEndSwapSheetIso`, not proved forced; the sheet family is exhibited, not proved unique.
-/

namespace DraismaVargas.Count.BallotEndSwapGeneral

open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.SlopeRigidity
open DraismaVargas.Count.BallotCoreIdentification
open DraismaVargas.Count.BallotValency
open DraismaVargas.Count.BallotEndSwapSheetIso (catStar_relabel_eq swap_pairval_iff)
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.W4StableSource

/-! ## 1.  The sheet family -/

/-- The sheet `1`, which is the label `cum s 1` of every slope sequence (`Slopes.cum_one`). -/
def sheetOne (m : ℕ) : Fin (m + 1 + 2) := ⟨1, by omega⟩

@[simp] theorem sheetOne_val (m : ℕ) : (sheetOne m).val = 1 := rfl

theorem sheetOne_ne_zero (m : ℕ) : sheetOne m ≠ 0 := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval

section Sheets

variable {m : ℕ} (s : Slopes (2 * (m + 1 + 1)))

/-- The label `cum s 2`, as a sheet of the degree-`(m + 3)` ballot datum.  It is `1` or `2`,
according as `s₂ = 1` or `s₂ = 3`. -/
def cumTwo : Fin (m + 1 + 2) :=
  ⟨s.cum 2, by have h := Slopes.cum_le s (m := m + 1) rfl 2; omega⟩

@[simp] theorem cumTwo_val : (cumTwo s).val = s.cum 2 := rfl

theorem cumTwo_ne_zero : cumTwo s ≠ 0 := by
  intro h
  have hval := congrArg Fin.val h
  have hpos := Slopes.one_le_cum s 2
  simp only [cumTwo_val, Fin.val_zero] at hval
  omega

/-- **The sheet permutation**: the transposition of `cum s 1 = 1` and `cum s 2`.  It is the
identity exactly when `s₂ = 1`. -/
def bSwap : Equiv.Perm (Fin (m + 1 + 2)) := Equiv.swap (sheetOne m) (cumTwo s)

theorem bSwap_zero : bSwap s 0 = 0 :=
  Equiv.swap_apply_of_ne_of_ne (Ne.symm (sheetOne_ne_zero m)) (Ne.symm (cumTwo_ne_zero s))

theorem bSwap_symm : (bSwap s).symm = bSwap s := Equiv.symm_swap _ _

theorem bSwap_trans : (bSwap s).trans (bSwap s) = Equiv.refl (Fin (m + 1 + 2)) :=
  Equiv.ext fun k ↦ Equiv.swap_apply_self (sheetOne m) (cumTwo s) k

/-! ## 2.  The membership dictionary at the near end, at every `m` -/

theorem vertPred_zero_iff (k : ℕ) : VertPred (m + 1) s 0 k ↔ (k = 0 ∨ k = 1) := by
  rw [vertPred_pair s (by decide) k, show lolli 0 = 1 from by unfold lolli; decide]
  show (k = 0 ∨ k = s.cum 1) ↔ _
  rw [Slopes.cum_one]

theorem vertPred_one_iff (k : ℕ) : VertPred (m + 1) s 1 k ↔ (k = 0 ∨ k = 1) := by
  rw [vertPred_pair s (by decide) k, show lolli 1 = 1 from by unfold lolli; decide]
  show (k = 0 ∨ k = s.cum 1) ↔ _
  rw [Slopes.cum_one]

theorem vertPred_three_iff (k : ℕ) : VertPred (m + 1) s 3 k ↔ (k = 0 ∨ k = s.cum 2) := by
  rw [vertPred_pair s (by decide) k, show lolli 3 = 2 from by unfold lolli; decide]
  rfl

theorem vertPred_four_iff (k : ℕ) : VertPred (m + 1) s 4 k ↔ (k = 0 ∨ k = s.cum 2) := by
  rw [vertPred_pair s (by decide) k, show lolli 4 = 2 from by unfold lolli; decide]
  rfl

theorem vertPred_two_iff (k : ℕ) : VertPred (m + 1) s 2 k ↔ s.VertMem 2 k := by
  rw [vertPred_junction s (by decide) k, show lolli 2 = 2 from by unfold lolli; decide]

theorem edgePred_zero_iff (k : ℕ) : EdgePred (m + 1) s 0 k ↔ k = 0 :=
  edgePred_leaf s (Or.inl (by decide)) k

theorem edgePred_three_iff (k : ℕ) : EdgePred (m + 1) s 3 k ↔ k = 0 :=
  edgePred_leaf s (Or.inl (by decide)) k

theorem edgePred_one_iff (k : ℕ) : EdgePred (m + 1) s 1 k ↔ (k = 0 ∨ k = 1) := by
  rw [edgePred_spine s (by decide) k, show (1 + 2) / 3 = 1 from by decide,
    Slopes.spineMem_one_iff_pairMem_one]
  show (k = 0 ∨ k = s.cum 1) ↔ _
  rw [Slopes.cum_one]

/-- The first stem.  The far leaf index `6 (m + 1) + 2` is the only place `m` enters
`EdgePred`, and it is not `2`. -/
theorem edgePred_two_iff (k : ℕ) : EdgePred (m + 1) s 2 k ↔ (k = 0 ∨ k = s.cum 2) := by
  rw [edgePred_stem s (by decide) (by omega) k, show (2 + 4) / 3 = 2 from by decide]
  rfl

/-! ## 3.  The moved partition equations -/

theorem bSwap_pairval (k : Fin (m + 1 + 2)) :
    (k.val = 0 ∨ k.val = 1) ↔ ((bSwap s k).val = 0 ∨ (bSwap s k).val = s.cum 2) :=
  swap_pairval_iff (a := sheetOne m) (b := cumTwo s) (sheetOne_ne_zero m) (cumTwo_ne_zero s) k

/-- The bridge pair at the root is carried onto the bridge pair at `u₂`. -/
theorem vertPart_relabel_zero_three :
    (catStar (m + 1) (VertPred (m + 1) s 0)).relabel (bSwap s) =
      catStar (m + 1) (VertPred (m + 1) s 3) := by
  refine catStar_relabel_eq _ _ _ (bSwap_zero s) fun k ↦ ?_
  rw [vertPred_zero_iff, vertPred_three_iff]
  exact bSwap_pairval s k

theorem vertPart_relabel_one_four :
    (catStar (m + 1) (VertPred (m + 1) s 1)).relabel (bSwap s) =
      catStar (m + 1) (VertPred (m + 1) s 4) := by
  refine catStar_relabel_eq _ _ _ (bSwap_zero s) fun k ↦ ?_
  rw [vertPred_one_iff, vertPred_four_iff]
  exact bSwap_pairval s k

theorem vertPart_relabel_three_zero :
    (catStar (m + 1) (VertPred (m + 1) s 3)).relabel (bSwap s) =
      catStar (m + 1) (VertPred (m + 1) s 0) := by
  conv_lhs => rw [← vertPart_relabel_zero_three s]
  rw [SheetPartition.relabel_relabel, bSwap_trans, Transport.DatumIso.relabel_refl]

theorem vertPart_relabel_four_one :
    (catStar (m + 1) (VertPred (m + 1) s 4)).relabel (bSwap s) =
      catStar (m + 1) (VertPred (m + 1) s 1) := by
  conv_lhs => rw [← vertPart_relabel_one_four s]
  rw [SheetPartition.relabel_relabel, bSwap_trans, Transport.DatumIso.relabel_refl]

/-- The spine block above `h₁` is carried onto the bridge pair above the first stem.  This is
the equation that the identity sheet layer cannot supply. -/
theorem edgePart_relabel_one_two :
    (catStar (m + 1) (EdgePred (m + 1) s 1)).relabel (bSwap s) =
      catStar (m + 1) (EdgePred (m + 1) s 2) := by
  refine catStar_relabel_eq _ _ _ (bSwap_zero s) fun k ↦ ?_
  rw [edgePred_one_iff, edgePred_two_iff]
  exact bSwap_pairval s k

theorem edgePart_relabel_two_one :
    (catStar (m + 1) (EdgePred (m + 1) s 2)).relabel (bSwap s) =
      catStar (m + 1) (EdgePred (m + 1) s 1) := by
  conv_lhs => rw [← edgePart_relabel_one_two s]
  rw [SheetPartition.relabel_relabel, bSwap_trans, Transport.DatumIso.relabel_refl]

/-- Both loops carry the discrete partition, which every permutation fixing `0` fixes. -/
theorem edgePart_relabel_zero_three :
    (catStar (m + 1) (EdgePred (m + 1) s 0)).relabel (bSwap s) =
      catStar (m + 1) (EdgePred (m + 1) s 3) := by
  refine catStar_relabel_eq _ _ _ (bSwap_zero s) fun k ↦ ?_
  rw [edgePred_zero_iff, edgePred_three_iff]
  constructor
  · intro hk
    have hk0 : k = 0 := Fin.ext (by rw [hk, Fin.val_zero])
    rw [hk0, bSwap_zero, Fin.val_zero]
  · intro hk
    have hk0 : bSwap s k = 0 := Fin.ext (by rw [hk, Fin.val_zero])
    have hh := congrArg (bSwap s) hk0
    rw [bSwap_zero, show bSwap s (bSwap s k) = k from
      Equiv.swap_apply_self (sheetOne m) (cumTwo s) k] at hh
    rw [hh, Fin.val_zero]

theorem edgePart_relabel_three_zero :
    (catStar (m + 1) (EdgePred (m + 1) s 3)).relabel (bSwap s) =
      catStar (m + 1) (EdgePred (m + 1) s 0) := by
  conv_lhs => rw [← edgePart_relabel_zero_three s]
  rw [SheetPartition.relabel_relabel, bSwap_trans, Transport.DatumIso.relabel_refl]

/-! ## 4.  The sheet families, indexed by target vertices and occurrences -/

/-- The sheet permutation at a target vertex: the transposition at the four moved vertices
`u₁ = 0`, `v₁ = 1`, `u₂ = 3`, `v₂ = 4`, the identity elsewhere. -/
def bVertexPerm (v : (catTree (m + 1)).V) : Equiv.Perm (Fin (m + 1 + 2)) :=
  if v.val = 0 ∨ v.val = 1 ∨ v.val = 3 ∨ v.val = 4 then bSwap s else Equiv.refl _

/-- The sheet permutation at a target occurrence: the transposition at the four moved
occurrences `0, 1, 2, 3`, the identity elsewhere. -/
def bEdgePerm (e : (catTree (m + 1)).edges) : Equiv.Perm (Fin (m + 1 + 2)) :=
  if edgeIndex (m + 1) e < 4 then bSwap s else Equiv.refl _

theorem bVertexPerm_moved {v : (catTree (m + 1)).V}
    (h : v.val = 0 ∨ v.val = 1 ∨ v.val = 3 ∨ v.val = 4) :
    bVertexPerm s v = bSwap s := ite_eq_left h

theorem bVertexPerm_fixed {v : (catTree (m + 1)).V}
    (h : ¬ (v.val = 0 ∨ v.val = 1 ∨ v.val = 3 ∨ v.val = 4)) :
    bVertexPerm s v = Equiv.refl _ := ite_eq_right h

theorem bEdgePerm_occ (i : Fin (6 * (m + 1) + 3)) :
    bEdgePerm s (occ (m + 1) i) = if i.val < 4 then bSwap s else Equiv.refl _ := by
  show (if edgeIndex (m + 1) (occ (m + 1) i) < 4 then bSwap s else Equiv.refl _) = _
  rw [edgeIndex_occ]

/-! ## 5.  Reading the two partitions off an index -/

theorem ballotVertexPart_of_val {v : (catTree (m + 1)).V} {a : ℕ} (h : v.val = a) :
    ballotVertexPart (m + 1) s v = catStar (m + 1) (VertPred (m + 1) s a) := by
  show catStar (m + 1) (VertPred (m + 1) s v.val) = _
  rw [h]

theorem ballotEdgePart_occ_of_val {i : Fin (6 * (m + 1) + 3)} {a : ℕ} (h : i.val = a) :
    ballotEdgePart (m + 1) s (occ (m + 1) i) = catStar (m + 1) (EdgePred (m + 1) s a) := by
  show catStar (m + 1) (EdgePred (m + 1) s (edgeIndex (m + 1) (occ (m + 1) i))) = _
  rw [edgeIndex_occ, h]

/-! ## 6.  The `compatible` obligation at the spine vertex `p₂` -/

/-- Sheet `1 = cum s 1` lies in the block above the spine vertex `p₂`: it is in the block of
the first spine edge, which is the bridge pair of the first lollipop. -/
theorem vertPred_two_one : VertPred (m + 1) s 2 1 := by
  rw [vertPred_two_iff]
  exact Or.inl ((Slopes.spineMem_one_iff_pairMem_one s 1).mpr (Or.inr (Slopes.cum_one s).symm))

/-- So does sheet `cum s 2`: it is the partner of the bridge pair over the first stem, and
`Slopes.vertMem_of_pairMem` puts that pair inside the spine-vertex block. -/
theorem vertPred_two_cumTwo : VertPred (m + 1) s 2 (s.cum 2) := by
  rw [vertPred_two_iff]
  exact Slopes.vertMem_of_pairMem s (Or.inr rfl)

/-- **The transposition is inner at the spine vertex `p₂`.**  `p₂` is fixed by the end swap
and carries the identity sheet permutation, so `compatible` there asks that the transposition
move every sheet inside its own block -- which it does, both swapped sheets lying in the block
of `VertMem s 2`. -/
theorem bSwap_rel_vertTwo (k : Fin (m + 1 + 2)) :
    (catStar (m + 1) (VertPred (m + 1) s 2)).Rel (bSwap s k) k := by
  rw [catStar_rel_iff _ (vertPred_zero s 2)]
  by_cases hk1 : k = sheetOne m
  · subst hk1
    refine Or.inl ⟨?_, vertPred_two_one s⟩
    rw [show bSwap s (sheetOne m) = cumTwo s from Equiv.swap_apply_left _ _]
    exact vertPred_two_cumTwo s
  · by_cases hk2 : k = cumTwo s
    · subst hk2
      refine Or.inl ⟨?_, vertPred_two_cumTwo s⟩
      rw [show bSwap s (cumTwo s) = sheetOne m from Equiv.swap_apply_right _ _]
      exact vertPred_two_one s
    · exact Or.inr (Equiv.swap_apply_of_ne_of_ne hk1 hk2)

/-! ## 7.  The self-isomorphism of the ballot gluing datum -/

/-- **The near end swap is a self-isomorphism of the ballot gluing datum, at every even genus
at least four and for every slope sequence.**  Its target layer is the one
`DraismaVargasCount.EndSwapRealized` uses for the caterpillar (`endSwapTgtEquiv m`,
`endSwapEdgeEquiv m`, `endSwap_ends m`); its sheet layer is the transposition
`(cum s 1, cum s 2)` at the four moved vertices and the four moved occurrences.  This is
`BallotEndSwapSheetIso.bEndSwapDatumIso`, there at `m = 1`. -/
noncomputable def bEndSwapDatumIso :
    GeometricDatumIso (ballotDatum (m + 1) s) (ballotDatum (m + 1) s) where
  targetVertex := endSwapTgtEquiv m
  targetEdge := endSwapEdgeEquiv m
  ends := endSwap_ends m
  vertexPerm := bVertexPerm s
  edgePerm := bEdgePerm s
  vertexPartition v := by
    show ballotVertexPart (m + 1) s (endSwapTgtEquiv m v) =
      (ballotVertexPart (m + 1) s v).relabel (bVertexPerm s v)
    by_cases hmoved : v.val = 0 ∨ v.val = 1 ∨ v.val = 3 ∨ v.val = 4
    · rw [bVertexPerm_moved s hmoved]
      have htgt : (endSwapTgtEquiv m v).val =
          if v.val = 0 then 3 else if v.val = 1 then 4 else if v.val = 3 then 0
            else if v.val = 4 then 1 else v.val := rfl
      rcases hmoved with h | h | h | h
      · rw [ballotVertexPart_of_val s (show (endSwapTgtEquiv m v).val = 3 by rw [htgt, ite_eq_left h]),
          ballotVertexPart_of_val s h, vertPart_relabel_zero_three]
      · rw [ballotVertexPart_of_val s
            (show (endSwapTgtEquiv m v).val = 4 by rw [htgt, ite_eq_right (by omega), ite_eq_left h]),
          ballotVertexPart_of_val s h, vertPart_relabel_one_four]
      · rw [ballotVertexPart_of_val s
            (show (endSwapTgtEquiv m v).val = 0 by
              rw [htgt, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]),
          ballotVertexPart_of_val s h, vertPart_relabel_three_zero]
      · rw [ballotVertexPart_of_val s
            (show (endSwapTgtEquiv m v).val = 1 by
              rw [htgt, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]),
          ballotVertexPart_of_val s h, vertPart_relabel_four_one]
    · rw [bVertexPerm_fixed s hmoved, Transport.DatumIso.relabel_refl,
        show endSwapTgtEquiv m v = v from endSwapTgtFun_fix m v (by tauto) (by tauto)
          (by tauto) (by tauto)]
  edgePartition e := by
    obtain ⟨i, rfl⟩ := occ_surj (m + 1) e
    show ballotEdgePart (m + 1) s (endSwapEdgeEquiv m (occ (m + 1) i)) =
      (ballotEdgePart (m + 1) s (occ (m + 1) i)).relabel (bEdgePerm s (occ (m + 1) i))
    rw [endSwapEdgeEquiv_occ, bEdgePerm_occ]
    have hlt := i.isLt
    have hslot : ((endSwap m).slot i).val =
        if i.val = 0 then 3 else if i.val = 1 then 2 else if i.val = 2 then 1
          else if i.val = 3 then 0 else i.val := endSwap_slot_val m i
    rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ 4 ≤ i.val by omega)
      with h | h | h | h | h
    · rw [ite_eq_left (by omega),
        ballotEdgePart_occ_of_val s (show ((endSwap m).slot i).val = 3 by rw [hslot, ite_eq_left h]),
        ballotEdgePart_occ_of_val s h, edgePart_relabel_zero_three]
    · rw [ite_eq_left (by omega),
        ballotEdgePart_occ_of_val s
          (show ((endSwap m).slot i).val = 2 by rw [hslot, ite_eq_right (by omega), ite_eq_left h]),
        ballotEdgePart_occ_of_val s h, edgePart_relabel_one_two]
    · rw [ite_eq_left (by omega),
        ballotEdgePart_occ_of_val s
          (show ((endSwap m).slot i).val = 1 by
            rw [hslot, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]),
        ballotEdgePart_occ_of_val s h, edgePart_relabel_two_one]
    · rw [ite_eq_left (by omega),
        ballotEdgePart_occ_of_val s
          (show ((endSwap m).slot i).val = 0 by
            rw [hslot, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]),
        ballotEdgePart_occ_of_val s h, edgePart_relabel_three_zero]
    · rw [ite_eq_right (by omega), Transport.DatumIso.relabel_refl,
        endSwap_slot_of_four_le m i h]
  compatible edge vertex hv sheet := by
    obtain ⟨i, rfl⟩ := occ_surj (m + 1) edge
    have hlt := i.isLt
    have hends : vertex.val = parentIndex (i.val + 1) ∨ vertex.val = i.val + 1 := by
      rcases hv with h | h
      · exact Or.inl (by rw [← h]; exact occ_fst_val (m + 1) i)
      · exact Or.inr (by rw [← h]; exact occ_snd_val (m + 1) i)
    by_cases hbig : 4 ≤ i.val
    · have hfix : ¬ (vertex.val = 0 ∨ vertex.val = 1 ∨ vertex.val = 3 ∨ vertex.val = 4) := by
        have hp := parentIndex_not_moved (v := i.val + 1) (by omega)
        omega
      rw [bEdgePerm_occ, ite_eq_right (by omega), bVertexPerm_fixed s hfix]
      rfl
    · have hval : vertex.val = 0 ∨ vertex.val = 1 ∨ vertex.val = 2 ∨ vertex.val = 3 ∨
          vertex.val = 4 := by
        unfold parentIndex at hends
        split_ifs at hends <;> omega
      rw [bEdgePerm_occ, ite_eq_left (by omega)]
      by_cases hmoved : vertex.val = 0 ∨ vertex.val = 1 ∨ vertex.val = 3 ∨ vertex.val = 4
      · rw [bVertexPerm_moved s hmoved, Equiv.symm_apply_apply]
        rfl
      · have hv2 : vertex.val = 2 := by tauto
        rw [bVertexPerm_fixed s hmoved]
        show (ballotVertexPart (m + 1) s vertex).Rel _ sheet
        rw [ballotVertexPart_of_val s hv2, Equiv.refl_symm, Equiv.refl_apply]
        exact bSwap_rel_vertTwo s sheet

@[simp] theorem bEndSwapDatumIso_targetVertex :
    (bEndSwapDatumIso s).targetVertex = endSwapTgtEquiv m := rfl

@[simp] theorem bEndSwapDatumIso_targetEdge :
    (bEndSwapDatumIso s).targetEdge = endSwapEdgeEquiv m := rfl

/-! ## 8.  The two `overCore` equations of `SlopeRigidity.Realizes` -/

/-- **The row dictionary moves by the slot part of the end swap.** -/
theorem bEndSwapDatumIso_rowIndex (hconn : (ballotDatum (m + 1) s).Connected)
    (edge : NonDanglingEdge (ballotDatum (m + 1) s)) :
    (ballotLabelling (m + 1) s).row ((bEndSwapDatumIso s).stablePathEquiv hconn edge.stablePath) =
      (endSwap m).slot ((ballotLabelling (m + 1) s).row edge.stablePath) := by
  rw [GeometricDatumIso.stablePathEquiv_mk]
  show (catEdgeEquiv (m + 1)).symm (endSwapEdgeEquiv m edge.1.1.1) =
    (endSwap m).slot ((catEdgeEquiv (m + 1)).symm edge.1.1.1)
  exact endSwapEdgeEquiv_symm_apply m _

/-- **The row half of `Realizes`**, the end swap being an involution on slots. -/
theorem bEndSwapDatumIso_overCore_row (hconn : (ballotDatum (m + 1) s).Connected)
    (path : StablePath (ballotDatum (m + 1) s)) :
    (endSwap m).slot
        ((ballotIdent (m + 1) s).row ((bEndSwapDatumIso s).stablePathEquiv hconn path)) =
      (ballotIdent (m + 1) s).row path := by
  induction path using Quot.inductionOn with
  | h edge =>
    show (endSwap m).slot ((ballotLabelling (m + 1) s).row
        ((bEndSwapDatumIso s).stablePathEquiv hconn edge.stablePath)) =
      (ballotLabelling (m + 1) s).row edge.stablePath
    rw [bEndSwapDatumIso_rowIndex s hconn edge]
    exact endSwapSlotFun_involutive m _

/-- **The vertex half of `Realizes`.**  `BallotCoreIdentification.ballotIdent` indexes a branch
vertex by `branchIdx` of its target vertex, so the caterpillar's arithmetic
`endSwapVtx_branchIdx` applies verbatim. -/
theorem bEndSwapDatumIso_overCore_vertex (hconn : (ballotDatum (m + 1) s).Connected)
    (b : BranchVertex (ballotDatum (m + 1) s)) :
    (endSwap m).vtx
        ((ballotIdent (m + 1) s).vertex ((bEndSwapDatumIso s).branchVertexEquiv hconn b)) =
      (ballotIdent (m + 1) s).vertex b := by
  apply Fin.ext
  show (endSwapVtxFun m ((ballotIdent (m + 1) s).vertex
      ((bEndSwapDatumIso s).branchVertexEquiv hconn b))).val = branchIdx b.1.1.1.val
  rw [endSwapVtxFun_val,
    show ((ballotIdent (m + 1) s).vertex ((bEndSwapDatumIso s).branchVertexEquiv hconn b)).val =
      branchIdx (endSwapTgtFun m b.1.1.1).val from rfl,
    endSwapTgtFun_val]
  exact endSwapVtx_branchIdx b.1.1.1.val

/-! ## 9.  The near end swap, realised -/

/-- **The near end swap is realised by every member of the ballot family, at every even genus
at least four**, over every slope sequence and every request whatsoever.  At `m = 1` this is
`BallotEndSwapSheetIso.ballotRealizes_endSwap`. -/
theorem ballotRealizes_endSwap (request : Fin (6 * (m + 1) + 3) → ℚ) :
    Realizes (endSwap m) (ballotFamilyMember (m + 1) request s) :=
  ⟨bEndSwapDatumIso s, bEndSwapDatumIso_overCore_vertex s _,
    bEndSwapDatumIso_overCore_row s _⟩

/-- **The product of the two end swaps is realised by every ballot member**, at every even
genus at least four: `realizes_comp` of the near end swap (above) and the far end swap
(`BallotFarEndSwap.ballotRealizes_farSwap`). -/
theorem ballotRealizes_nearFarSwap (request : Fin (6 * (m + 1) + 3) → ℚ) :
    Realizes (BallotFarEndSwap.nearFarSwap m) (ballotFamilyMember (m + 1) request s) :=
  BallotFarEndSwap.realizes_comp (ballotRealizes_endSwap s request)
    (BallotFarEndSwap.ballotRealizes_farSwap s request)

end Sheets

/-- At `Slopes.six = [2, 3, 4, 3, 2]`, at genus six, the label `cum s 2` is `2`. -/
theorem cumTwo_six : (cumTwo (m := 1) Slopes.six).val = 2 := rfl

/-- **So the sheet layer is not the identity there**: `bSwap Slopes.six` is the transposition
`(1 2)`.  The identity sheet layer does not work at this `s`
(`BallotEndSwapSheetIso.bSwap_six_ne_refl` is the same fact). -/
theorem bSwap_six_ne_refl : bSwap (m := 1) Slopes.six ≠ Equiv.refl (Fin (1 + 1 + 2)) := by
  intro h
  have h1 : (bSwap (m := 1) Slopes.six (sheetOne 1)).val = 1 := by rw [h]; rfl
  rw [show bSwap (m := 1) Slopes.six (sheetOne 1) = cumTwo Slopes.six from
      Equiv.swap_apply_left _ _, cumTwo_six] at h1
  exact absurd h1 (by decide)

/-! ## 10.  The identity branch, `hStab`, and the base count at every `m ≥ 1` -/

section BaseCount

variable {m : ℕ}

/-- **The identity branch of `hStab` is realised at every even genus at least six.**  Every
relabelling of `catCore (m + 1)` acting as the identity on the interior spine slots is one of
the Klein four-group `{1, endSwap m, farSwap m, nearFarSwap m}`
(`BallotStabiliserReduction.left_end_determined`, `right_end_determined`,
`identity_branch_unique`), and each of the four is realised by every ballot member.  This is
`BallotFarEndSwap.identity_branch_realized_genusSix` (with `hFar_genusSix` inlined) at every
`m`. -/
theorem identity_branch_realized (hm : 1 ≤ m) (s : Slopes (2 * (m + 1 + 1)))
    (request : Fin (6 * (m + 1) + 3) → ℚ) (d : Relabel (catCore (m + 1)) (catCore (m + 1)))
    (hid : ∀ a, a < 2 * (m + 1) - 1 → BallotOrbit.innerIndex d a = a) :
    Realizes d (ballotFamilyMember (m + 1) request s) := by
  have hm' : 2 ≤ m + 1 := by omega
  rcases BallotStabiliserReduction.right_end_determined hm' d hid with hR | hR
  · rcases BallotStabiliserReduction.left_end_determined hm' d hid with hL | hL
    · have htriv := BallotStabiliserReduction.identity_branch_trivial_of_ends_fixed hm' d hid
        (fun e he ↦ hL.2.1 e he) (fun e he ↦ hR.2.2.1 e he)
      exact realizes_of_trivial htriv.1 htriv.2 _
    · have hde : d = endSwap m :=
        BallotStabiliserReduction.identity_branch_unique hm' d (endSwap m) hid
          (fun a ha ↦ BallotStabiliserReduction.innerIndex_endSwap m a ha)
          (fun e he ↦ by
            rw [hL.2.1 e he, endSwap_slot_apply, endSwapSlotFun_val]
            split_ifs <;> omega)
          (fun e he ↦ by
            rw [hR.2.2.1 e he, endSwap_slot_apply, endSwapSlotFun_val]
            split_ifs <;> omega)
      rw [hde]
      exact ballotRealizes_endSwap s request
  · rcases BallotStabiliserReduction.left_end_determined hm' d hid with hL | hL
    · have hd : d = BallotFarEndSwap.farSwap m :=
        BallotStabiliserReduction.identity_branch_unique hm' d (BallotFarEndSwap.farSwap m) hid
          (fun a ha ↦ BallotFarEndSwap.innerIndex_farSwap m a ha)
          (fun e he ↦ by
            rw [hL.2.1 e he, BallotFarEndSwap.farSwap_slot_val]
            split_ifs <;> first | contradiction | omega)
          (fun e he ↦ by
            rw [hR.2.2.1 e he, BallotFarEndSwap.farSwap_slot_val]
            split_ifs <;> first | contradiction | omega)
      rw [hd]
      exact BallotFarEndSwap.ballotRealizes_farSwap s request
    · have hd : d = BallotFarEndSwap.nearFarSwap m :=
        BallotStabiliserReduction.identity_branch_unique hm' d (BallotFarEndSwap.nearFarSwap m)
          hid (fun a ha ↦ BallotFarEndSwap.innerIndex_nearFarSwap m a ha)
          (fun e he ↦ by rw [hL.2.1 e he, BallotFarEndSwap.nearFarSwap_slot_one m e he])
          (fun e he ↦ by
            rw [hR.2.2.1 e he, BallotFarEndSwap.nearFarSwap_slot_far m e (by omega)]
            omega)
      rw [hd]
      exact ballotRealizes_nearFarSwap s request

/-- **`hStab` at every even genus at least six**: every relabelling of `catCore (m + 1)`
stabilising a ballot core diagonal is realised by that ballot member, over every request.  The
every-`m` form of `BallotSpineReversalSheetIso.hStab_genusSix`. -/
theorem hStab (hm : 1 ≤ m) (request : Fin (6 * (m + 1) + 3) → ℚ) :
    ∀ (s : Slopes (2 * (m + 1 + 1))) (d : Relabel (catCore (m + 1)) (catCore (m + 1))),
      (∀ slot, BallotSlopes.ballotCoreDiag (m + 1) s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag (m + 1) s slot) →
        Realizes d (ballotFamilyMember (m + 1) request s) :=
  BallotSpineReversalSheetIso.hStab_of_identity (m + 1) request
    (fun s d hid ↦ identity_branch_realized hm s request d hid)

/-- **Every member of the caterpillar fibre lies in a ballot class**, at every even genus at
least six, with no openness, oddness or request hypothesis. -/
theorem cls_eq_ballot (hm : 1 ≤ m) (request : Fin (6 * (m + 1) + 3) → ℚ)
    (mem : FibreMember (catCore (m + 1)) request (m + 1 + 2)) :
    ∃ s : Slopes (2 * (m + 1 + 1)), GeometricFibre.cls mem =
      GeometricFibre.cls (ballotFamilyMember (m + 1) request s) := by
  obtain ⟨rep, hD, hcls, -, -⟩ := CaterpillarAllMembers.exists_diagonal_rep mem
  obtain ⟨s, hs⟩ := CaterpillarAllMembers.cls_eq_ballot_of_diagonal (hStab hm request) rep hD
  exact ⟨s, hcls.symm.trans hs⟩

/-- **Every member of the caterpillar fibre has multiplicity exactly one**, at every even genus
at least six. -/
theorem absMult_eq_one (hm : 1 ≤ m) (request : Fin (6 * (m + 1) + 3) → ℚ)
    (mem : FibreMember (catCore (m + 1)) request (m + 1 + 2)) : mem.absMult = 1 := by
  obtain ⟨s, hs⟩ := cls_eq_ballot hm request mem
  have h := congrArg GeometricFibre.absMult hs
  simp only [GeometricFibre.absMult_cls] at h
  rw [h, ballotFamilyMember_absMult]

/-- The diagonal classification `BallotSlopes.DiagonalClassification (m + 1)` at every request,
at every even genus at least six, obtained without using oddness. -/
theorem diagonalClassification (hm : 1 ≤ m) (request : Fin (6 * (m + 1) + 3) → ℚ) :
    BallotSlopes.DiagonalClassification (m + 1) request where
  diagonal mem hOpen hOdd := by
    obtain ⟨rep, hD, hcls, hO, hM⟩ := CaterpillarAllMembers.exists_diagonal_rep mem
    exact ⟨rep, hO.mpr hOpen, hM.mpr hOdd, hD, hcls⟩
  extract mem _ _ hD := BallotResidues.exists_coreDiag_eq_ballotCoreDiag mem hD
  rigid first second _ _ hD₁ _ _ hD₂ heq := by
    obtain ⟨s, hs⟩ := BallotResidues.exists_coreDiag_eq_ballotCoreDiag first hD₁
    rw [CaterpillarAllMembers.cls_eq_ballot_of_coreDiag (hStab hm request) first hD₁ s hs,
      CaterpillarAllMembers.cls_eq_ballot_of_coreDiag (hStab hm request) second hD₂ s
        (heq ▸ hs)]

/-- **The integer base count at every even genus at least six.**  At a positive request the
fibre over the caterpillar of loops `catCore (m + 1)` has exactly `catalan (m + 2)` open
classes, and each has multiplicity one (`absMult_eq_one`).  At `m = 1` this is
`CaterpillarAllMembers.card_open_genusSix` (`C₃ = 5`); at `m = 2` it is `C₄ = 14`. -/
theorem card_open (hm : 1 ≤ m) {request : Fin (6 * (m + 1) + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    Nat.card {c : GeometricFibre (catCore (m + 1)) request (m + 1 + 2) // c.Open} =
      catalan (m + 2) := by
  have hOddAll : ∀ c : GeometricFibre (catCore (m + 1)) request (m + 1 + 2), c.IsOdd := by
    intro c
    obtain ⟨mem, rfl⟩ := GeometricFibre.cls_surjective c
    exact (GeometricFibre.isOdd_cls_iff mem).mpr
      (FibreMember.hasOddMult_of_absMult_eq_one (absMult_eq_one hm request mem))
  have hcount := openOddCount_eq_catalan' (m + 1) hRequest (diagonalClassification hm request)
  rw [← hcount, GeometricFibre.openOddCount]
  exact Nat.card_congr
    { toFun := fun c ↦ ⟨c.1, c.2, hOddAll c.1⟩
      invFun := fun c ↦ ⟨c.1, c.2.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

end BaseCount

end DraismaVargas.Count.BallotEndSwapGeneral
