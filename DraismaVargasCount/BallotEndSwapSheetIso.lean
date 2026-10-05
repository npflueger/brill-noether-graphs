module

public import DraismaVargasCount.BallotCoreIdentification
public import DraismaVargasCount.EndSwapRealized

@[expose] public section

/-!
# The end swap is a self-isomorphism of the ballot gluing datum at genus six

This module realises the end swap `SlopeRigidity.endSwap 1` on the ballot member
of every genus-six slope sequence.  That is one relabelling covered by the
`hStab` hypothesis of
`DiagonalClassificationGenusSix.diagonalClassification_genusSix_of_sharp_residues`:
every relabelling of `catCore 2` that stabilises a ballot core diagonal is
realised by the corresponding ballot member, part of the uniqueness half of
Vargas, Part II (arXiv:2609.09109), `prop-caterpillar-ballot` (a slope sequence
determines its morphism).  `BallotStabiliserReduction` reduces `hStab` to the two end swaps and
the spine reversal, and `BallotSpineReversalSheetIso.hStab_genusSix` assembles it;
`CaterpillarAllMembers` uses that for the base count over the caterpillar of
loops (step 1 of `DraismaVargasCount/Assembly.lean`).

## Why the sheet layer is not the identity

`SlopeRigidity.endSwapSheetIso` puts the identity sheet permutation at every
vertex and occurrence, which needs the target automorphism to preserve both
partitions.  On ballot data at genus six the end swap does not: at `Slopes.six`
the root `u₁` carries the block `{0, 1}` and its image `u₂` the block `{0, 2}`,
and the first spine edge carries `{0, 1}` while its image, the first stem,
carries `{0, 2}` (`vertPred_zero_iff`, `vertPred_three_iff`, `edgePred_one_iff`,
`edgePred_two_iff`, `cumTwo_six`).  This happens although
`SlopeRigidity.endSwap_stabilises_ballotCoreDiag` holds for every `s`.  The
`vertexPerm`/`edgePerm` fields of `GeometricDatumIso` supply the missing
freedom.

**This module uses them.**  It builds the self-isomorphism directly, with the
sheet transposition `(cum s 1, cum s 2)` at the four moved target vertices
`0, 1, 3, 4` and the four moved target occurrences `0, 1, 2, 3`, and the
identity everywhere else.

## Why that permutation, in one paragraph

Above the root `u₁` and its folded tip `v₁` the glued block is the bridge pair
`PairMem s 1 = {0, cum s 1} = {0, 1}`; above their images `u₂`, `v₂` it is
`PairMem s 2 = {0, cum s 2}`.  Along the first spine edge it is
`SpineMem s 1`, which *equals* `PairMem s 1` (`Slopes.spineMem_one_iff_pairMem_one`);
along its image, the first stem, it is `PairMem s 2` again.  The two loops carry
the discrete partition at both ends.  So every moved partition is a two-element
star, and one transposition carries each to its image -- `swap_pairval_iff` is
that computation, and `catStar_relabel_eq` turns it into the `relabel`
equations.  The `compatible` field is then free except at the spine vertex `p₂`,
which is fixed by the end swap and so carries the identity: there one needs both
`cum s 1` and `cum s 2` to lie in the *same* block of `VertMem s 2`, which is
`Slopes.spineMem_one_iff_pairMem_one` for the first and
`Slopes.vertMem_of_pairMem` for the second.

Note that `cum s 1 = 1` always (`Slopes.cum_one`) and `cum s 2 ∈ {1, 2}`, so on
the two slope sequences of genus six with `s₂ = 1` the transposition is the
identity: on those two the end swap does preserve both partitions, and the
construction has the identity sheet layer.

## What is proved

* `catStar_repr`, `catStar_relabel_eq` -- relabelling a star partition by a
  permutation fixing sheet `0` is again the star partition of the transported
  predicate.
* `or_val_iff`, `swap_pair_iff`, `swap_pairval_iff` -- a transposition
  `(a b)` with `a, b ≠ 0` carries the pair `{0, a}` onto `{0, b}`.
* `cumTwo`, `bSwap`, `bVertexPerm`, `bEdgePerm` -- the sheet family.
* `bSwap_zero`, `bSwap_symm`, `bSwap_trans` -- its three properties.
* `vertPred_zero_iff`, `vertPred_one_iff`, `vertPred_two_iff`,
  `vertPred_three_iff`, `vertPred_four_iff`, `edgePred_zero_iff`,
  `edgePred_one_iff`, `edgePred_two_iff`, `edgePred_three_iff` -- the genus-six
  membership dictionary at the five moved vertices, the four moved occurrences
  and the spine vertex `p₂`.
* `vertPart_relabel_zero_three`, `vertPart_relabel_one_four`,
  `vertPart_relabel_three_zero`, `vertPart_relabel_four_one`,
  `edgePart_relabel_one_two`, `edgePart_relabel_two_one`,
  `edgePart_relabel_zero_three`, `edgePart_relabel_three_zero` -- the moved
  partition equations.
* `vertPred_two_one`, `vertPred_two_cumTwo`, `bSwap_rel_vertTwo` -- the
  `compatible` obligation at the one fixed vertex that meets a moved occurrence.
* **`bEndSwapDatumIso s : GeometricDatumIso (ballotDatum 2 s) (ballotDatum 2 s)`**
  -- the sheet-carrying self-isomorphism, for **every** `s : Slopes 6`.
* `bEndSwapDatumIso_targetVertex`, `bEndSwapDatumIso_targetEdge` -- it lies over
  `endSwapTgtEquiv 1` and `endSwapEdgeEquiv 1`, the tree-level reading of
  `SlopeRigidity.endSwap 1` that `DraismaVargasCount.EndSwapRealized` uses.
* `bEndSwapDatumIso_rowIndex`, `bEndSwapDatumIso_overCore_row`,
  `bEndSwapDatumIso_overCore_vertex` -- the two `overCore` equations of
  `SlopeRigidity.Realizes`, read through
  `BallotCoreIdentification.ballotIdent`.
* **`ballotRealizes_endSwap s request : Realizes (endSwap 1)`
  `(ballotFamilyMember 2 request s)`** -- the headline, for every `s : Slopes 6`
  and **every** request whatsoever.
* `hStab_at_endSwap` -- the same, written in the exact shape of the `hStab`
  hypothesis of
  `DiagonalClassificationGenusSix.diagonalClassification_genusSix_of_sharp_residues`.
* `cumTwo_six`, `bSwap_six_ne_refl` -- at `Slopes.six`, where the end swap
  preserves neither partition, the sheet permutation is a genuine
  transposition, so the construction does not reduce to the identity sheet
  layer.

## Scope

* **One relabelling of `hStab`.**  `hStab` quantifies over *every*
  `d : CoreRelabel.Relabel (catCore 2) (catCore 2)` stabilising the ballot core
  diagonal; this module treats one `d`, namely `SlopeRigidity.endSwap 1`, and
  does not enumerate the others.  `BallotStabiliserReduction` reduces the rest
  to the relabellings that move the far end of the spine and those that
  reverse it; the sheet-carrying isomorphisms over the far end swap and over
  the spine reversal (`SpineReversal.spineReversal`) are built in
  `BallotFarEndSwap` and `BallotSpineReversalSheetIso`, and
  `BallotSpineReversalSheetIso.hStab_genusSix` is the whole of `hStab` at
  genus six.
* **No other hypothesis is treated.**  `hTrivalent`, `hThree` and `hSupply` of
  `diagonalClassification_genusSix_of_sharp_residues` are not addressed here,
  and neither is `BallotSlopes.DiagonalClassification 2 request`.
* **The target layer is chosen, not derived.**  `endSwapTgtEquiv 1` and
  `endSwapEdgeEquiv 1` are the tree-level reading
  `DraismaVargasCount.EndSwapRealized` uses; that the `ends` field forces them
  is not proved here.  Likewise the sheet family is exhibited, not proved
  unique.
* **Genus six only.**  Nothing here is stated at general `m`; the index
  arithmetic of `VertPred`/`EdgePred` is done at `m = 2` throughout.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no
  `#eval`.
-/

namespace DraismaVargas.Count.BallotEndSwapSheetIso

open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.SlopeRigidity
open DraismaVargas.Count.BallotCoreIdentification
open DraismaVargas.Count.BallotValency
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.W4StableSource

/-! ## 1.  Relabelling a star partition -/

/-- The representative map of `catStar`, as a rewrite. -/
theorem catStar_repr {m : ℕ} (P : ℕ → Prop) [DecidablePred P] (k : Fin (m + 2)) :
    (catStar m P).repr k = if P k.val then 0 else k := rfl

/-- **Relabelling a star partition transports its predicate.**  A permutation
fixing the spine sheet `0` carries `catStar m P` to `catStar m Q` as soon as it
intertwines the two predicates. -/
theorem catStar_relabel_eq {m : ℕ} (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (σ : Equiv.Perm (Fin (m + 2))) (hσ : σ 0 = 0)
    (h : ∀ k : Fin (m + 2), P k.val ↔ Q (σ k).val) :
    (catStar m P).relabel σ = catStar m Q := by
  apply SheetPartition.ext_repr
  funext i
  show σ ((catStar m P).repr (σ.symm i)) = (catStar m Q).repr i
  rw [catStar_repr, catStar_repr]
  by_cases hP : P (σ.symm i).val
  · rw [ite_eq_left hP, hσ, ite_eq_left]
    have hQ := (h (σ.symm i)).mp hP
    rwa [Equiv.apply_symm_apply] at hQ
  · rw [ite_eq_right hP, Equiv.apply_symm_apply, ite_eq_right]
    intro hQ
    exact hP ((h (σ.symm i)).mpr (by rwa [Equiv.apply_symm_apply]))

/-! ## 2.  A transposition carries one bridge pair onto the other -/

/-- Membership of `{0, x}`, read on indices or on elements. -/
theorem or_val_iff {n : ℕ} (k x : Fin (n + 1)) :
    (k.val = 0 ∨ k.val = x.val) ↔ (k = 0 ∨ k = x) := by
  constructor
  · rintro (h | h)
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **The transposition `(a b)` carries `{0, a}` onto `{0, b}`**, for any two
sheets `a, b` other than `0`. -/
theorem swap_pair_iff {n : ℕ} {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) (k : Fin (n + 1)) :
    (k = 0 ∨ k = a) ↔ (Equiv.swap a b k = 0 ∨ Equiv.swap a b k = b) := by
  have hswap0 : Equiv.swap a b (0 : Fin (n + 1)) = 0 :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl hswap0
    · exact Or.inr (Equiv.swap_apply_left _ _)
  · rintro (h | h)
    · refine Or.inl ?_
      have hh := congrArg (Equiv.swap a b) h
      rwa [Equiv.swap_apply_self, hswap0] at hh
    · refine Or.inr ?_
      have hh := congrArg (Equiv.swap a b) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at hh

/-- The same, on sheet indices -- the shape `PairMem` is stated in. -/
theorem swap_pairval_iff {n : ℕ} {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (k : Fin (n + 1)) :
    (k.val = 0 ∨ k.val = a.val) ↔
      ((Equiv.swap a b k).val = 0 ∨ (Equiv.swap a b k).val = b.val) :=
  (or_val_iff k a).trans ((swap_pair_iff ha hb k).trans (or_val_iff _ b).symm)


/-! ## 3.  The sheet family -/

variable (s : Slopes (2 * (2 + 1)))

/-- The label `cum s 2`, as a sheet of the degree-four ballot datum.  It is `2`
on the three genus-six slope sequences with `s₂ = 3` and `1` on the other
two. -/
def cumTwo : Fin (2 + 2) :=
  ⟨s.cum 2, by have h := Slopes.cum_le s (m := 2) rfl 2; omega⟩

@[simp] theorem cumTwo_val : (cumTwo s).val = s.cum 2 := rfl

theorem cumTwo_ne_zero : cumTwo s ≠ 0 := by
  intro h
  have hval : (cumTwo s).val = 0 := by rw [h]; rfl
  have hpos := Slopes.one_le_cum s 2
  rw [cumTwo_val] at hval
  omega

/-- **The sheet permutation**: the transposition of `cum s 1 = 1` and
`cum s 2`.  It is the identity exactly when `s₂ = 1`. -/
def bSwap : Equiv.Perm (Fin (2 + 2)) := Equiv.swap 1 (cumTwo s)

theorem bSwap_zero : bSwap s 0 = 0 :=
  Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm (cumTwo_ne_zero s))

theorem bSwap_symm : (bSwap s).symm = bSwap s := Equiv.symm_swap _ _

theorem bSwap_trans : (bSwap s).trans (bSwap s) = Equiv.refl (Fin (2 + 2)) :=
  Equiv.ext fun k ↦ Equiv.swap_apply_self 1 (cumTwo s) k

/-! ## 4.  The membership dictionary at genus six -/

theorem vertPred_zero_iff (k : ℕ) : VertPred 2 s 0 k ↔ (k = 0 ∨ k = 1) := by
  rw [vertPred_pair s (by decide) k, show lolli 0 = 1 from by unfold lolli; decide]
  show (k = 0 ∨ k = s.cum 1) ↔ _
  rw [Slopes.cum_one]

theorem vertPred_one_iff (k : ℕ) : VertPred 2 s 1 k ↔ (k = 0 ∨ k = 1) := by
  rw [vertPred_pair s (by decide) k, show lolli 1 = 1 from by unfold lolli; decide]
  show (k = 0 ∨ k = s.cum 1) ↔ _
  rw [Slopes.cum_one]

theorem vertPred_three_iff (k : ℕ) : VertPred 2 s 3 k ↔ (k = 0 ∨ k = s.cum 2) := by
  rw [vertPred_pair s (by decide) k, show lolli 3 = 2 from by unfold lolli; decide]
  rfl

theorem vertPred_four_iff (k : ℕ) : VertPred 2 s 4 k ↔ (k = 0 ∨ k = s.cum 2) := by
  rw [vertPred_pair s (by decide) k, show lolli 4 = 2 from by unfold lolli; decide]
  rfl

theorem vertPred_two_iff (k : ℕ) : VertPred 2 s 2 k ↔ s.VertMem 2 k := by
  rw [vertPred_junction s (by decide) k, show lolli 2 = 2 from by unfold lolli; decide]

theorem edgePred_zero_iff (k : ℕ) : EdgePred 2 s 0 k ↔ k = 0 :=
  edgePred_leaf s (Or.inl (by decide)) k

theorem edgePred_three_iff (k : ℕ) : EdgePred 2 s 3 k ↔ k = 0 :=
  edgePred_leaf s (Or.inl (by decide)) k

theorem edgePred_one_iff (k : ℕ) : EdgePred 2 s 1 k ↔ (k = 0 ∨ k = 1) := by
  rw [edgePred_spine s (by decide) k, show (1 + 2) / 3 = 1 from by decide,
    Slopes.spineMem_one_iff_pairMem_one]
  show (k = 0 ∨ k = s.cum 1) ↔ _
  rw [Slopes.cum_one]

theorem edgePred_two_iff (k : ℕ) : EdgePred 2 s 2 k ↔ (k = 0 ∨ k = s.cum 2) := by
  rw [edgePred_stem s (by decide) (by decide) k, show (2 + 4) / 3 = 2 from by decide]
  rfl

/-! ## 5.  The five moved partition equations -/

theorem bSwap_pairval (k : Fin (2 + 2)) :
    (k.val = 0 ∨ k.val = 1) ↔ ((bSwap s k).val = 0 ∨ (bSwap s k).val = s.cum 2) :=
  swap_pairval_iff (a := (1 : Fin (2 + 2))) (b := cumTwo s) (by decide)
    (cumTwo_ne_zero s) k

/-- The bridge pair at the root is carried onto the bridge pair at `u₂`. -/
theorem vertPart_relabel_zero_three :
    (catStar 2 (VertPred 2 s 0)).relabel (bSwap s) = catStar 2 (VertPred 2 s 3) := by
  refine catStar_relabel_eq _ _ _ (bSwap_zero s) fun k ↦ ?_
  rw [vertPred_zero_iff, vertPred_three_iff]
  exact bSwap_pairval s k

theorem vertPart_relabel_one_four :
    (catStar 2 (VertPred 2 s 1)).relabel (bSwap s) = catStar 2 (VertPred 2 s 4) := by
  refine catStar_relabel_eq _ _ _ (bSwap_zero s) fun k ↦ ?_
  rw [vertPred_one_iff, vertPred_four_iff]
  exact bSwap_pairval s k

theorem vertPart_relabel_three_zero :
    (catStar 2 (VertPred 2 s 3)).relabel (bSwap s) = catStar 2 (VertPred 2 s 0) := by
  conv_lhs => rw [← vertPart_relabel_zero_three s]
  rw [SheetPartition.relabel_relabel, bSwap_trans, Transport.DatumIso.relabel_refl]

theorem vertPart_relabel_four_one :
    (catStar 2 (VertPred 2 s 4)).relabel (bSwap s) = catStar 2 (VertPred 2 s 1) := by
  conv_lhs => rw [← vertPart_relabel_one_four s]
  rw [SheetPartition.relabel_relabel, bSwap_trans, Transport.DatumIso.relabel_refl]

/-- The spine block above `h₁` is carried onto the bridge pair above the first
stem.  This is the equation that the identity sheet layer of `endSwapSheetIso`
cannot supply. -/
theorem edgePart_relabel_one_two :
    (catStar 2 (EdgePred 2 s 1)).relabel (bSwap s) = catStar 2 (EdgePred 2 s 2) := by
  refine catStar_relabel_eq _ _ _ (bSwap_zero s) fun k ↦ ?_
  rw [edgePred_one_iff, edgePred_two_iff]
  exact bSwap_pairval s k

theorem edgePart_relabel_two_one :
    (catStar 2 (EdgePred 2 s 2)).relabel (bSwap s) = catStar 2 (EdgePred 2 s 1) := by
  conv_lhs => rw [← edgePart_relabel_one_two s]
  rw [SheetPartition.relabel_relabel, bSwap_trans, Transport.DatumIso.relabel_refl]

/-- Both loops carry the discrete partition, which every permutation fixes. -/
theorem edgePart_relabel_zero_three :
    (catStar 2 (EdgePred 2 s 0)).relabel (bSwap s) = catStar 2 (EdgePred 2 s 3) := by
  refine catStar_relabel_eq _ _ _ (bSwap_zero s) fun k ↦ ?_
  rw [edgePred_zero_iff, edgePred_three_iff]
  constructor
  · intro hk
    have hk0 : k = 0 := Fin.ext hk
    rw [hk0, bSwap_zero]
    rfl
  · intro hk
    have hk0 : bSwap s k = 0 := Fin.ext hk
    have hh := congrArg (bSwap s) hk0
    rw [bSwap_zero, show bSwap s (bSwap s k) = k from Equiv.swap_apply_self 1 (cumTwo s) k] at hh
    rw [hh]
    rfl

theorem edgePart_relabel_three_zero :
    (catStar 2 (EdgePred 2 s 3)).relabel (bSwap s) = catStar 2 (EdgePred 2 s 0) := by
  conv_lhs => rw [← edgePart_relabel_zero_three s]
  rw [SheetPartition.relabel_relabel, bSwap_trans, Transport.DatumIso.relabel_refl]


/-! ## 6.  The sheet families, indexed by target vertices and occurrences -/

/-- The sheet permutation at a target vertex: the transposition at the four
moved vertices `u₁ = 0`, `v₁ = 1`, `u₂ = 3`, `v₂ = 4`, the identity elsewhere. -/
def bVertexPerm (v : (catTree 2).V) : Equiv.Perm (Fin (2 + 2)) :=
  if v.val = 0 ∨ v.val = 1 ∨ v.val = 3 ∨ v.val = 4 then bSwap s else Equiv.refl _

/-- The sheet permutation at a target occurrence: the transposition at the four
moved occurrences `0, 1, 2, 3`, the identity elsewhere. -/
def bEdgePerm (e : (catTree 2).edges) : Equiv.Perm (Fin (2 + 2)) :=
  if edgeIndex 2 e < 4 then bSwap s else Equiv.refl _

theorem bVertexPerm_moved {v : (catTree 2).V}
    (h : v.val = 0 ∨ v.val = 1 ∨ v.val = 3 ∨ v.val = 4) :
    bVertexPerm s v = bSwap s := ite_eq_left h

theorem bVertexPerm_fixed {v : (catTree 2).V}
    (h : ¬ (v.val = 0 ∨ v.val = 1 ∨ v.val = 3 ∨ v.val = 4)) :
    bVertexPerm s v = Equiv.refl _ := ite_eq_right h

theorem bEdgePerm_occ (i : Fin (6 * 2 + 3)) :
    bEdgePerm s (occ 2 i) = if i.val < 4 then bSwap s else Equiv.refl _ := by
  show (if edgeIndex 2 (occ 2 i) < 4 then bSwap s else Equiv.refl _) = _
  rw [edgeIndex_occ]

/-! ## 7.  Reading the two partitions off an index -/

theorem ballotVertexPart_of_val {v : (catTree 2).V} {a : ℕ} (h : v.val = a) :
    ballotVertexPart 2 s v = catStar 2 (VertPred 2 s a) := by
  show catStar 2 (VertPred 2 s v.val) = _
  rw [h]

theorem ballotEdgePart_occ_of_val {i : Fin (6 * 2 + 3)} {a : ℕ} (h : i.val = a) :
    ballotEdgePart 2 s (occ 2 i) = catStar 2 (EdgePred 2 s a) := by
  show catStar 2 (EdgePred 2 s (edgeIndex 2 (occ 2 i))) = _
  rw [edgeIndex_occ, h]

/-! ## 8.  The `compatible` obligation at the spine vertex `p₂` -/

/-- Sheet `1 = cum s 1` lies in the block above the spine vertex `p₂`: it is in
the block of the first spine edge, which is the bridge pair of the first
lollipop. -/
theorem vertPred_two_one : VertPred 2 s 2 1 := by
  rw [vertPred_two_iff]
  exact Or.inl ((Slopes.spineMem_one_iff_pairMem_one s 1).mpr (Or.inr (Slopes.cum_one s).symm))

/-- So does sheet `cum s 2`: it is the partner of the bridge pair over the first
stem, and `Slopes.vertMem_of_pairMem` puts that pair inside the spine-vertex
block. -/
theorem vertPred_two_cumTwo : VertPred 2 s 2 (s.cum 2) := by
  rw [vertPred_two_iff]
  exact Slopes.vertMem_of_pairMem s (Or.inr rfl)

/-- **The transposition is inner at the spine vertex `p₂`.**  `p₂` is fixed by
the end swap and carries the identity sheet permutation, so `compatible` there
asks that the transposition move every sheet inside its own block -- which it
does, both swapped sheets lying in the block of `VertMem s 2`. -/
theorem bSwap_rel_vertTwo (k : Fin (2 + 2)) :
    (catStar 2 (VertPred 2 s 2)).Rel (bSwap s k) k := by
  rw [catStar_rel_iff _ (vertPred_zero s 2)]
  by_cases hk1 : k = 1
  · subst hk1
    refine Or.inl ⟨?_, vertPred_two_one s⟩
    rw [show bSwap s 1 = cumTwo s from Equiv.swap_apply_left _ _]
    exact vertPred_two_cumTwo s
  · by_cases hk2 : k = cumTwo s
    · subst hk2
      refine Or.inl ⟨?_, vertPred_two_cumTwo s⟩
      rw [show bSwap s (cumTwo s) = 1 from Equiv.swap_apply_right _ _]
      exact vertPred_two_one s
    · exact Or.inr (Equiv.swap_apply_of_ne_of_ne hk1 hk2)

/-! ## 9.  The self-isomorphism of the ballot gluing datum -/

/-- **The end swap is a self-isomorphism of the ballot gluing datum at genus
six, for every slope sequence.**  Its target layer is the one
`DraismaVargasCount.EndSwapRealized` uses for the caterpillar
(`endSwapTgtEquiv 1`, `endSwapEdgeEquiv 1`, `endSwap_ends 1`); its sheet layer
is the transposition `(cum s 1, cum s 2)` at the four moved vertices and the
four moved occurrences.  At `Slopes.six` the identity sheet layer cannot do
this (`bSwap_six_ne_refl` and the module docstring). -/
noncomputable def bEndSwapDatumIso :
    GeometricDatumIso (ballotDatum 2 s) (ballotDatum 2 s) where
  targetVertex := endSwapTgtEquiv 1
  targetEdge := endSwapEdgeEquiv 1
  ends := endSwap_ends 1
  vertexPerm := bVertexPerm s
  edgePerm := bEdgePerm s
  vertexPartition v := by
    show ballotVertexPart 2 s (endSwapTgtEquiv 1 v) =
      (ballotVertexPart 2 s v).relabel (bVertexPerm s v)
    by_cases hmoved : v.val = 0 ∨ v.val = 1 ∨ v.val = 3 ∨ v.val = 4
    · rw [bVertexPerm_moved s hmoved]
      have htgt : (endSwapTgtEquiv 1 v).val =
          if v.val = 0 then 3 else if v.val = 1 then 4 else if v.val = 3 then 0
            else if v.val = 4 then 1 else v.val := rfl
      rcases hmoved with h | h | h | h
      · rw [ballotVertexPart_of_val s (show (endSwapTgtEquiv 1 v).val = 3 by rw [htgt, ite_eq_left h]),
          ballotVertexPart_of_val s h, vertPart_relabel_zero_three]
      · rw [ballotVertexPart_of_val s
            (show (endSwapTgtEquiv 1 v).val = 4 by rw [htgt, ite_eq_right (by omega), ite_eq_left h]),
          ballotVertexPart_of_val s h, vertPart_relabel_one_four]
      · rw [ballotVertexPart_of_val s
            (show (endSwapTgtEquiv 1 v).val = 0 by
              rw [htgt, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]),
          ballotVertexPart_of_val s h, vertPart_relabel_three_zero]
      · rw [ballotVertexPart_of_val s
            (show (endSwapTgtEquiv 1 v).val = 1 by
              rw [htgt, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]),
          ballotVertexPart_of_val s h, vertPart_relabel_four_one]
    · rw [bVertexPerm_fixed s hmoved, Transport.DatumIso.relabel_refl,
        show endSwapTgtEquiv 1 v = v from endSwapTgtFun_fix 1 v (by tauto) (by tauto)
          (by tauto) (by tauto)]
  edgePartition e := by
    obtain ⟨i, rfl⟩ := occ_surj 2 e
    show ballotEdgePart 2 s (endSwapEdgeEquiv 1 (occ 2 i)) =
      (ballotEdgePart 2 s (occ 2 i)).relabel (bEdgePerm s (occ 2 i))
    rw [endSwapEdgeEquiv_occ, bEdgePerm_occ]
    have hlt := i.isLt
    have hslot : ((endSwap 1).slot i).val =
        if i.val = 0 then 3 else if i.val = 1 then 2 else if i.val = 2 then 1
          else if i.val = 3 then 0 else i.val := endSwap_slot_val 1 i
    rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ 4 ≤ i.val by omega)
      with h | h | h | h | h
    · rw [ite_eq_left (by omega),
        ballotEdgePart_occ_of_val s (show ((endSwap 1).slot i).val = 3 by rw [hslot, ite_eq_left h]),
        ballotEdgePart_occ_of_val s h, edgePart_relabel_zero_three]
    · rw [ite_eq_left (by omega),
        ballotEdgePart_occ_of_val s
          (show ((endSwap 1).slot i).val = 2 by rw [hslot, ite_eq_right (by omega), ite_eq_left h]),
        ballotEdgePart_occ_of_val s h, edgePart_relabel_one_two]
    · rw [ite_eq_left (by omega),
        ballotEdgePart_occ_of_val s
          (show ((endSwap 1).slot i).val = 1 by
            rw [hslot, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]),
        ballotEdgePart_occ_of_val s h, edgePart_relabel_two_one]
    · rw [ite_eq_left (by omega),
        ballotEdgePart_occ_of_val s
          (show ((endSwap 1).slot i).val = 0 by
            rw [hslot, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]),
        ballotEdgePart_occ_of_val s h, edgePart_relabel_three_zero]
    · rw [ite_eq_right (by omega), Transport.DatumIso.relabel_refl,
        endSwap_slot_of_four_le 1 i h]
  compatible edge vertex hv sheet := by
    obtain ⟨i, rfl⟩ := occ_surj 2 edge
    have hlt := i.isLt
    have hends : vertex.val = parentIndex (i.val + 1) ∨ vertex.val = i.val + 1 := by
      rcases hv with h | h
      · exact Or.inl (by rw [← h]; exact occ_fst_val 2 i)
      · exact Or.inr (by rw [← h]; exact occ_snd_val 2 i)
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
        show (ballotVertexPart 2 s vertex).Rel _ sheet
        rw [ballotVertexPart_of_val s hv2, Equiv.refl_symm, Equiv.refl_apply]
        exact bSwap_rel_vertTwo s sheet

@[simp] theorem bEndSwapDatumIso_targetVertex :
    (bEndSwapDatumIso s).targetVertex = endSwapTgtEquiv 1 := rfl

@[simp] theorem bEndSwapDatumIso_targetEdge :
    (bEndSwapDatumIso s).targetEdge = endSwapEdgeEquiv 1 := rfl


/-! ## 10.  The two `overCore` equations of `SlopeRigidity.Realizes` -/

/-- **The row dictionary moves by the slot part of the end swap.**  The ballot
labelling's row equivalence is "the target occurrence the stable row lies over"
(`BallotCoreIdentification.row_bMainND`), which is the same reading
`DraismaVargasCount.EndSwapRealized` uses for the caterpillar, so this is the same
computation. -/
theorem bEndSwapDatumIso_rowIndex (hconn : (ballotDatum 2 s).Connected)
    (edge : NonDanglingEdge (ballotDatum 2 s)) :
    (ballotLabelling 2 s).row ((bEndSwapDatumIso s).stablePathEquiv hconn edge.stablePath) =
      (endSwap 1).slot ((ballotLabelling 2 s).row edge.stablePath) := by
  rw [GeometricDatumIso.stablePathEquiv_mk]
  show (catEdgeEquiv 2).symm (endSwapEdgeEquiv 1 edge.1.1.1) =
    (endSwap 1).slot ((catEdgeEquiv 2).symm edge.1.1.1)
  exact endSwapEdgeEquiv_symm_apply 1 _

/-- **The row half of `Realizes`**, the end swap being an involution on
slots. -/
theorem bEndSwapDatumIso_overCore_row (hconn : (ballotDatum 2 s).Connected)
    (path : StablePath (ballotDatum 2 s)) :
    (endSwap 1).slot ((ballotIdent 2 s).row ((bEndSwapDatumIso s).stablePathEquiv hconn path)) =
      (ballotIdent 2 s).row path := by
  induction path using Quot.inductionOn with
  | h edge =>
    show (endSwap 1).slot ((ballotLabelling 2 s).row
        ((bEndSwapDatumIso s).stablePathEquiv hconn edge.stablePath)) =
      (ballotLabelling 2 s).row edge.stablePath
    rw [bEndSwapDatumIso_rowIndex s hconn edge]
    exact endSwapSlotFun_involutive 1 _

/-- **The vertex half of `Realizes`.**  `BallotCoreIdentification.ballotIdent`
indexes a branch vertex by `branchIdx` of its target vertex
(`ballotIdent_vertex_val`, a `rfl`), exactly as `FibreCaterpillar.catIdent`
does, so the caterpillar's arithmetic `endSwapVtx_branchIdx` applies
verbatim. -/
theorem bEndSwapDatumIso_overCore_vertex (hconn : (ballotDatum 2 s).Connected)
    (b : BranchVertex (ballotDatum 2 s)) :
    (endSwap 1).vtx ((ballotIdent 2 s).vertex ((bEndSwapDatumIso s).branchVertexEquiv hconn b)) =
      (ballotIdent 2 s).vertex b := by
  apply Fin.ext
  show (endSwapVtxFun 1 ((ballotIdent 2 s).vertex
      ((bEndSwapDatumIso s).branchVertexEquiv hconn b))).val = branchIdx b.1.1.1.val
  rw [endSwapVtxFun_val,
    show ((ballotIdent 2 s).vertex ((bEndSwapDatumIso s).branchVertexEquiv hconn b)).val =
      branchIdx (endSwapTgtFun 1 b.1.1.1).val from rfl,
    endSwapTgtFun_val]
  exact endSwapVtx_branchIdx b.1.1.1.val

/-! ## 11.  The obligation, discharged on the end-swap subgroup -/

/-- **The end swap is realised by every member of the ballot family at genus
six**, over every request whatsoever: no positivity and no genericity.  This is
the `Realizes` conclusion of `hStab`'s consequent at `d = endSwap 1`, for all
five slope sequences. -/
theorem ballotRealizes_endSwap (request : Fin (6 * 2 + 3) → ℚ) :
    Realizes (endSwap 1) (ballotFamilyMember 2 request s) :=
  ⟨bEndSwapDatumIso s, bEndSwapDatumIso_overCore_vertex s _,
    bEndSwapDatumIso_overCore_row s _⟩


/-- **The `hStab` instance at `d = endSwap 1`**, written in the exact shape of
that hypothesis of
`DiagonalClassificationGenusSix.diagonalClassification_genusSix_of_sharp_residues`.
The stabiliser premise is not used: it holds for every `s` anyway
(`SlopeRigidity.endSwap_stabilises_ballotCoreDiag` at `m = 1`), and the
conclusion holds for every `s` unconditionally. -/
theorem hStab_at_endSwap (request : Fin (6 * 2 + 3) → ℚ)
    (_hstab : ∀ slot, BallotSlopes.ballotCoreDiag 2 s ((endSwap 1).slot.symm slot) =
      BallotSlopes.ballotCoreDiag 2 s slot) :
    Realizes (endSwap 1) (ballotFamilyMember 2 request s) :=
  ballotRealizes_endSwap s request

/-! ## 12.  The sheet layer is not the identity -/

/-- At `Slopes.six = [2, 3, 4, 3, 2]`, where the end swap preserves neither
partition, the label `cum s 2` is `2`. -/
theorem cumTwo_six : (cumTwo Slopes.six).val = 2 := rfl

/-- **So the sheet layer really is non-trivial there.**  The identity sheet
permutations of `endSwapSheetIso` do not work at this `s`: the root carries the
block `{0, 1}` and its image the block `{0, 2}`.  `bSwap Slopes.six` is the
transposition `(1 2)`. -/
theorem bSwap_six_ne_refl : bSwap Slopes.six ≠ Equiv.refl (Fin (2 + 2)) := by
  intro h
  have h1 : (bSwap Slopes.six 1).val = 1 := by rw [h]; rfl
  rw [show bSwap Slopes.six 1 = cumTwo Slopes.six from Equiv.swap_apply_left _ _,
    cumTwo_six] at h1
  exact absurd h1 (by decide)

end DraismaVargas.Count.BallotEndSwapSheetIso
