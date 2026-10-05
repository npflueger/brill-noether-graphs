module

public import DraismaVargasCount.SlopeStack
public import DraismaVargasCount.StarPartition
public import DraismaVargas.LocalCases.CaterpillarDatum

@[expose] public section

/-!
# The ballot-parametrized caterpillar gluing datum

**Source.**  Vargas, Part II (arXiv:2609.09109):
`lm:combinatorial-structure-caterpillar-of-loops` (the target tree is `T^CL_g`, uniquely) and
part (2) of `prop-caterpillar-ballot` (every slope sequence determines a full-dimensional
tropical morphism).  This module constructs one gluing datum `ballotDatum m s` over
`catTree m` for each slope sequence `s : Slopes (2 * (m + 1))`, proves `GluingDatum.Valid` for
every one of them, and identifies it with Part I's caterpillar datum at the distinguished
sequence.

## The construction

The degree is `d = g/2 + 1 = m + 2`; sheet `0` is the spine sheet.  Every
partition used is a **star partition** (`SheetPartition.sheetStar`, from `StarPartition`):
one block through sheet `0`, singletons elsewhere.  Writing `s_i` for the slope on the spine
edge `h_i` and `cum s i` for the number of labels introduced up to `h_i`
(`DraismaVargasCount.SlopeStack`), the blocks are

| target piece | block | size |
|---|---|---|
| spine edge `h_i` | `SpineMem s i = {0} ∪ [cum i - s_i + 2, cum i]` | `s_i` |
| spine vertex `p_i` | `VertMem s i = SpineMem s (i-1) ∪ SpineMem s i` | `max (s_{i-1}, s_i) = m(B_i)` |
| stem `p_i u_i`, and `u_i`, `v_i` | `PairMem s i = {0, cum i}` | `2` |
| leaf edge `u_i v_i` | `{0}`, i.e. the discrete partition | `1` |

Refinement at `p_i` is exactly the nestedness of consecutive spine blocks,
which is why the labels have to be introduced by a counter that never reuses a
discarded one: that is what makes the source **connected**
(`Slopes.exists_cum_eq`).  The two ends of the spine carry no stem, and there
the spine block and the bridge pair coincide, since `s_1 = s_{g-1} = 2`.

## What is proved

* `ballotDatum m s : GluingDatum (catTree m) (m + 2)`, with both refinement
  receipts (§3).
* `ballotDatum_riemannHurwitz`, `ballotDatum_connected`, `ballotDatum_valid`
  (§4, §5) -- uniformly in `m` and in `s`, with no `decide` and no fixed genus.
  Riemann--Hurwitz is automatic at every vertex of valency at most two
  (`rh_valency_one`, `rh_valency_two`, which hold for *every* datum over
  `catTree m`) and is the equality `2 m(B_i) = s_{i-1} + s_i + 1` at the
  `g - 2` junctions.
* `ballotDatum_zig : ballotDatum m (zig m) = caterpillarDatum m` (§6) -- at the
  distinguished ballot sequence `(2,1,2,1,…,2)` this datum **is** Part I's
  `LocalCases.CaterpillarDatum.caterpillarDatum m`, as an equality of gluing
  data, not merely an isomorphism.  That is the compatibility that keeps
  `CaterpillarRows`, `CaterpillarSeed` and `Count.FibreCaterpillar` usable from
  the parametrized family.
* `stem_blockCount`, `spine_blockCount_back`, `spine_blockCount_forward`,
  `spine_dangling_total` (§7) -- the census of grafted dangling paths at a junction.

## The grafted paths at a junction, compared with Part II

In the proof of part (2) of `prop-caterpillar-ballot`, Part II restores balancing at `B_i`
by attaching `m(B_i) - 2` paths of length two that map to the lollipop at `B_i`, and orients
them by the sign of `s_i - s_{i-1} = ±1`.  The construction here differs from that
description as follows.  Harmonicity at `B_i` demands total index `m(B_i)` in **each** of the
three directions, and `s_{i-1} + s_i = 2 m(B_i) - 1` leaves a deficit of `1` on exactly one
of the two spine directions.  So the source carries, at `B_i`, `m(B_i) - 2` length-two
dangling paths into the lollipop **and one further index-one edge along the spine**, on the
lower side of the step; it is that edge, not the lollipop paths, that the sign of
`s_i - s_{i-1}` orients.  §7 proves both halves (`spine_dangling_total` is the "exactly
one").  The construction here is the one forced by harmonicity.

## What is not proved here

* **No `FullDimensionalSourcePresentation`, no `FibreMember`, no count.**  This
  module produces a valid gluing datum and nothing more.  The labelling, the
  `SeedDeterminant.DiagonalPattern` and the determinant are
  `BallotValency.ballotFullDim`; `absMult = 1` is `BallotMultiplicity`; the fibre
  members are `BallotCoreIdentification.ballotFamilyMember`, and that every member
  over the caterpillar is one of them is `CaterpillarAllMembers`.  No statement below
  mentions `FibreMember`, `catCore`, `GeometricFibre` or `openOddCount`.
* **No uniqueness.**  That the datum of a full-dimensional morphism over a
  metric caterpillar of loops is one of these (Part II, `prop-caterpillar-ballot`) is
  not proved, nor stated.  Nothing here rules out other data over `catTree m`.
* **No genericity hypothesis is used or supplied.**  Part II's count
  (`prop-divisors-on-chain`) assumes the edge lengths of the metric
  caterpillar are *pairwise distinct*; that hypothesis belongs to the
  uniqueness half and does not enter the construction here, which is purely
  combinatorial and mentions no lengths at all.
* The genus of the source is **not** proved in this module; it is
  `Count.BallotDatum.genus_sourceGraph_ballotDatum`.
* `Slopes g` is used only through `Count.Slopes` and `DraismaVargasCount.SlopeStack`; the
  hypothesis `g = 2 * (m + 1)` is built into the type of the argument `s` and
  is never assumed silently elsewhere.
-/
namespace DraismaVargas.Count.BallotDatum

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.Infrastructure.SheetPartition (sheetStar)
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.Count

variable {m : ℕ}

/-! ## 1.  The star partition at degree `m + 2` -/

/-- The star partition of the `m + 2` sheets cut out by `P`. -/
def catStar (m : ℕ) (P : ℕ → Prop) [DecidablePred P] : SheetPartition (m + 2) :=
  sheetStar (m + 1) P

theorem catStar_rel_iff (P : ℕ → Prop) [DecidablePred P] (hP0 : P 0)
    (i j : Fin (m + 2)) :
    (catStar m P).Rel i j ↔ ((P i.val ∧ P j.val) ∨ i = j) :=
  SheetPartition.sheetStar_rel_iff P hP0 i j

theorem catStar_refines (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hP0 : P 0) (hQ0 : Q 0) (hsub : ∀ k, P k → Q k) :
    (catStar m P).Refines (catStar m Q) :=
  SheetPartition.sheetStar_refines P Q hP0 hQ0 hsub

theorem catStar_blockCard_of_mem (P : ℕ → Prop) [DecidablePred P] (hP0 : P 0)
    {σ : Fin (m + 2)} (hσ : P σ.val) :
    (catStar m P).blockCard σ = ((Finset.range (m + 2)).filter P).card :=
  SheetPartition.sheetStar_blockCard_of_mem P hP0 hσ

theorem catStar_blockCard_of_not (P : ℕ → Prop) [DecidablePred P] (hP0 : P 0)
    {σ : Fin (m + 2)} (hσ : ¬ P σ.val) : (catStar m P).blockCard σ = 1 :=
  SheetPartition.sheetStar_blockCard_of_not P hP0 hσ

theorem catStar_blockCountWithin_of_mem (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hP0 : P 0) (hQ0 : Q 0)
    (hsub : ∀ k, P k → Q k) {σ : Fin (m + 2)} (hσ : Q σ.val) :
    (catStar m P).blockCountWithin (catStar m Q) σ
      = 1 + (((Finset.range (m + 2)).filter Q).card
          - ((Finset.range (m + 2)).filter P).card) :=
  SheetPartition.sheetStar_blockCountWithin_of_mem P Q hP0 hQ0 hsub hσ

theorem catStar_blockCountWithin_of_not (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hQ0 : Q 0) {σ : Fin (m + 2)}
    (hσ : ¬ Q σ.val) : (catStar m P).blockCountWithin (catStar m Q) σ = 1 :=
  SheetPartition.sheetStar_blockCountWithin_of_not P Q hQ0 hσ

theorem catStar_eq_discrete (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ k, P k ↔ k = 0) : catStar m P = SheetPartition.discrete (m + 2) :=
  SheetPartition.sheetStar_eq_discrete P hP

/-- Part I's `pairPart m j` is the star partition of `{0, j}`. -/
theorem catStar_eq_pairPart (P : ℕ → Prop) [DecidablePred P] (j : ℕ)
    (hP : ∀ k, P k ↔ (k = 0 ∨ k = j)) : catStar m P = pairPart m j := by
  apply SheetPartition.ext_repr
  funext k
  show (if P k.val then (0 : Fin (m + 2)) else k)
    = (if k.val = j then (0 : Fin (m + 2)) else k)
  by_cases h : k.val = j
  · rw [ite_eq_left h, ite_eq_left ((hP _).mpr (Or.inr h))]
  · by_cases h0 : k.val = 0
    · rw [ite_eq_right h, ite_eq_left ((hP _).mpr (Or.inl h0))]
      exact (Fin.ext h0).symm
    · have hPk : ¬ P k.val := by
        intro hh
        rcases (hP k.val).mp hh with hk | hk
        · exact h0 hk
        · exact h hk
      rw [ite_eq_right h, ite_eq_right hPk]

theorem card_blocks_catStar (P : ℕ → Prop) [DecidablePred P] (hP0 : P 0) :
    Fintype.card (catStar m P).Blocks
      = (m + 2) + 1 - ((Finset.range (m + 2)).filter P).card :=
  SheetPartition.card_blocks_sheetStar P hP0

/-! ## 2.  The two membership predicates on the caterpillar tree -/

variable (m) in
/-- The sheets glued at the target vertex numbered `a`: the spine-vertex block
at a junction (`a % 3 = 2`, which includes the exceptional `u_g = 6m+2`), the
bridge pair at every other vertex. -/
def VertPred (s : Slopes (2 * (m + 1))) (a k : ℕ) : Prop :=
  if a % 3 = 2 then s.VertMem (lolli a) k else s.PairMem (lolli a) k

instance (s : Slopes (2 * (m + 1))) (a : ℕ) : DecidablePred (VertPred m s a) := by
  intro k; unfold VertPred; infer_instance

variable (m) in
/-- The sheets glued along the target occurrence numbered `e`: the spine block
over a spine edge (`e % 3 = 1`), the bridge pair over a stem (`e % 3 = 2`
except the exceptional leaf index `6m+2`), and the singleton `{0}` -- i.e. the
discrete partition -- over each of the `g` leaf edges. -/
def EdgePred (s : Slopes (2 * (m + 1))) (e k : ℕ) : Prop :=
  if e % 3 = 1 then s.SpineMem ((e + 2) / 3) k
  else if e % 3 = 2 ∧ e ≠ 6 * m + 2 then s.PairMem ((e + 4) / 3) k
  else k = 0

instance (s : Slopes (2 * (m + 1))) (e : ℕ) : DecidablePred (EdgePred m s e) := by
  intro k; unfold EdgePred; infer_instance

theorem vertPred_junction (s : Slopes (2 * (m + 1))) {a : ℕ} (h : a % 3 = 2) (k : ℕ) :
    VertPred m s a k ↔ s.VertMem (lolli a) k := by unfold VertPred; rw [ite_eq_left h]

theorem vertPred_pair (s : Slopes (2 * (m + 1))) {a : ℕ} (h : a % 3 ≠ 2) (k : ℕ) :
    VertPred m s a k ↔ s.PairMem (lolli a) k := by unfold VertPred; rw [ite_eq_right h]

theorem edgePred_spine (s : Slopes (2 * (m + 1))) {e : ℕ} (h : e % 3 = 1) (k : ℕ) :
    EdgePred m s e k ↔ s.SpineMem ((e + 2) / 3) k := by unfold EdgePred; rw [ite_eq_left h]

theorem edgePred_stem (s : Slopes (2 * (m + 1))) {e : ℕ} (h : e % 3 = 2)
    (h2 : e ≠ 6 * m + 2) (k : ℕ) :
    EdgePred m s e k ↔ s.PairMem ((e + 4) / 3) k := by
  unfold EdgePred; rw [ite_eq_right (by omega), ite_eq_left ⟨h, h2⟩]

theorem edgePred_leaf (s : Slopes (2 * (m + 1))) {e : ℕ}
    (h : e % 3 = 0 ∨ e = 6 * m + 2) (k : ℕ) : EdgePred m s e k ↔ k = 0 := by
  unfold EdgePred
  rcases h with h | h
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · subst h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by simp)]

@[simp] theorem vertPred_zero (s : Slopes (2 * (m + 1))) (a : ℕ) :
    VertPred m s a 0 := by
  unfold VertPred
  by_cases h : a % 3 = 2
  · rw [ite_eq_left h]; exact Slopes.vertMem_zero s _
  · rw [ite_eq_right h]; exact Slopes.pairMem_zero s _

@[simp] theorem edgePred_zero (s : Slopes (2 * (m + 1))) (e : ℕ) :
    EdgePred m s e 0 := by
  unfold EdgePred
  by_cases h : e % 3 = 1
  · rw [ite_eq_left h]; exact Slopes.spineMem_zero s _
  · rw [ite_eq_right h]
    by_cases h2 : e % 3 = 2 ∧ e ≠ 6 * m + 2
    · rw [ite_eq_left h2]; exact Slopes.pairMem_zero s _
    · rw [ite_eq_right h2]


/-! ## 3.  The refinement receipts, and the datum

Over a spine edge the block `S_i` sits inside the union `S_{i-1} ∪ S_i` at the
spine vertex behind it and inside `S_i ∪ S_{i+1}` at the one in front; over a
stem the bridge pair sits inside the spine-vertex block by
`Slopes.vertMem_of_pairMem`; over a leaf edge the partition is discrete and
refines everything.  The one boundary case is the first spine edge, whose
parent is the root `u_1`, where `S_1` and the bridge pair coincide
(`Slopes.spineMem_one_iff_pairMem_one`). -/

/-- The block over an occurrence sits inside the block at its child endpoint. -/
theorem edgePred_child (s : Slopes (2 * (m + 1))) {e : ℕ} (he : e ≤ 6 * m + 2)
    (k : ℕ) (h : EdgePred m s e k) : VertPred m s (e + 1) k := by
  by_cases hspine : e % 3 = 1
  · rw [edgePred_spine s hspine] at h
    rw [vertPred_junction s (show (e + 1) % 3 = 2 by omega)]
    refine Slopes.vertMem_of_spineMem_left s ?_
    have hidx : lolli (e + 1) - 1 = (e + 2) / 3 := by unfold lolli; omega
    rw [hidx]
    exact h
  · by_cases hstem : e % 3 = 2 ∧ e ≠ 6 * m + 2
    · rw [edgePred_stem s hstem.1 hstem.2] at h
      rw [vertPred_pair s (show (e + 1) % 3 ≠ 2 by omega)]
      have hidx : lolli (e + 1) = (e + 4) / 3 := by unfold lolli; omega
      rw [hidx]
      exact h
    · rw [edgePred_leaf s (by omega) ] at h
      subst h
      exact vertPred_zero s _

/-- The block over an occurrence sits inside the block at its parent endpoint. -/
theorem edgePred_parent (s : Slopes (2 * (m + 1))) {e : ℕ} (he : e ≤ 6 * m + 2)
    (k : ℕ) (h : EdgePred m s e k) : VertPred m s (parentIndex (e + 1)) k := by
  by_cases hspine : e % 3 = 1
  · rw [edgePred_spine s hspine] at h
    have hpar : parentIndex (e + 1) = e - 2 := by
      unfold parentIndex; rw [ite_eq_left (show (e + 1) % 3 = 2 by omega)]; omega
    rw [hpar]
    rcases Nat.lt_or_ge e 4 with hsmall | hbig
    · -- the first spine edge: its parent is the root `u_1`
      have he1 : e = 1 := by omega
      subst he1
      rw [vertPred_pair s (show (1 - 2) % 3 ≠ 2 by norm_num)]
      have hl : lolli (1 - 2) = 1 := by unfold lolli; norm_num
      rw [hl]
      exact (Slopes.spineMem_one_iff_pairMem_one s k).mp
        (by simpa using h)
    · rw [vertPred_junction s (show (e - 2) % 3 = 2 by omega)]
      refine Slopes.vertMem_of_spineMem_right s ?_
      have hidx : lolli (e - 2) = (e + 2) / 3 := by unfold lolli; omega
      rw [hidx]
      exact h
  · by_cases hstem : e % 3 = 2 ∧ e ≠ 6 * m + 2
    · rw [edgePred_stem s hstem.1 hstem.2] at h
      have hpar : parentIndex (e + 1) = e := by
        unfold parentIndex; rw [ite_eq_right (show ¬ ((e + 1) % 3 = 2) by omega)]; omega
      rw [hpar, vertPred_junction s hstem.1]
      refine Slopes.vertMem_of_pairMem s ?_
      have hidx : lolli e = (e + 4) / 3 := by unfold lolli; omega
      rw [hidx]
      exact h
    · rw [edgePred_leaf s (by omega)] at h
      subst h
      exact vertPred_zero s _

/-- The vertex partition of the ballot-parametrized datum. -/
def ballotVertexPart (m : ℕ) (s : Slopes (2 * (m + 1))) (v : (catTree m).V) :
    SheetPartition (m + 2) :=
  catStar m (VertPred m s v.val)

/-- The occurrence partition of the ballot-parametrized datum. -/
def ballotEdgePart (m : ℕ) (s : Slopes (2 * (m + 1))) (e : (catTree m).edges) :
    SheetPartition (m + 2) :=
  catStar m (EdgePred m s (edgeIndex m e))

/-- **The ballot-parametrized caterpillar gluing datum** of degree
`d = g/2 + 1 = m + 2`, one for each slope sequence of genus `g = 2m + 2`. -/
def ballotDatum (m : ℕ) (s : Slopes (2 * (m + 1))) :
    GluingDatum (catTree m) (m + 2) where
  degree_pos := by omega
  vertexPartition := ballotVertexPart m s
  edgePartition := ballotEdgePart m s
  refines_left := by
    intro e
    obtain ⟨i, rfl⟩ := occ_surj m e
    have hi := i.isLt
    have hval : ((occ m i : (catTree m).edges) :
        (catTree m).V × (catTree m).V).1.val = parentIndex (i.val + 1) := rfl
    show (catStar m (EdgePred m s (edgeIndex m (occ m i)))).Refines
      (catStar m (VertPred m s ((occ m i : (catTree m).edges) :
        (catTree m).V × (catTree m).V).1.val))
    rw [edgeIndex_occ, hval]
    exact catStar_refines _ _ (edgePred_zero s _) (vertPred_zero s _)
      (fun k hk => edgePred_parent s (by omega) k hk)
  refines_right := by
    intro e
    obtain ⟨i, rfl⟩ := occ_surj m e
    have hi := i.isLt
    have hval : ((occ m i : (catTree m).edges) :
        (catTree m).V × (catTree m).V).2.val = i.val + 1 := rfl
    show (catStar m (EdgePred m s (edgeIndex m (occ m i)))).Refines
      (catStar m (VertPred m s ((occ m i : (catTree m).edges) :
        (catTree m).V × (catTree m).V).2.val))
    rw [edgeIndex_occ, hval]
    exact catStar_refines _ _ (edgePred_zero s _) (vertPred_zero s _)
      (fun k hk => edgePred_child s (by omega) k hk)

@[simp] theorem ballotDatum_vertexPartition (m : ℕ) (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) :
    (ballotDatum m s).vertexPartition v = ballotVertexPart m s v := rfl

@[simp] theorem ballotDatum_edgePartition (m : ℕ) (s : Slopes (2 * (m + 1)))
    (e : (catTree m).edges) :
    (ballotDatum m s).edgePartition e = ballotEdgePart m s e := rfl


/-! ## 4.  Riemann--Hurwitz

At a leaf and at a divalent vertex the condition is automatic: with `k` incident
occurrences the inequality reads `∑ c_e - 2 ≥ q (k - 2)`, and for `k ≤ 2` the
right-hand side is at most zero while every `c_e` and `q` is at least one.  The
whole content sits at the `g - 2` junctions `p_i`, where it is the equality
`2 m(B_i) = s_{i-1} + s_i + 1` of `prop-caterpillar-ballot`(1) -- i.e.
`r_φ(B_i) = 0`. -/

section Generic

variable (data : GluingDatum (catTree m) (m + 2))

/-- Riemann--Hurwitz at a leaf of the target holds for **every** datum. -/
theorem rh_valency_one (v : (catTree m).V) {a : Fin (6 * m + 3)}
    (hS : incidentIndices m v = {a}) :
    data.RiemannHurwitzAtTargetVertex v := by
  intro sheet
  have h1 := SheetPartition.blockCountWithin_pos
    (data.edgePartition (occ m a)) (data.vertexPartition v) sheet
  have h2 := (data.vertexPartition v).blockCard_pos sheet
  rw [card_incidentEdges_one m v hS,
    sum_incidentEdges_one m v hS
      (fun e => ((data.edgePartition e).blockCountWithin
        (data.vertexPartition v) sheet : ℤ))]
  push_cast
  omega

/-- Riemann--Hurwitz at a divalent target vertex holds for **every** datum. -/
theorem rh_valency_two (v : (catTree m).V) {a b : Fin (6 * m + 3)}
    (hab : a ≠ b) (hS : incidentIndices m v = {a, b}) :
    data.RiemannHurwitzAtTargetVertex v := by
  intro sheet
  have h1 := SheetPartition.blockCountWithin_pos
    (data.edgePartition (occ m a)) (data.vertexPartition v) sheet
  have h2 := SheetPartition.blockCountWithin_pos
    (data.edgePartition (occ m b)) (data.vertexPartition v) sheet
  rw [card_incidentEdges_two m v hab hS,
    sum_incidentEdges_two m v hab hS
      (fun e => ((data.edgePartition e).blockCountWithin
        (data.vertexPartition v) sheet : ℤ))]
  push_cast
  omega

end Generic

/-! ### Reading the block sizes off the predicates -/

theorem card_filter_congr (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ k, P k ↔ Q k) :
    ((Finset.range (m + 2)).filter P).card
      = ((Finset.range (m + 2)).filter Q).card := by
  classical
  have : (Finset.range (m + 2)).filter P = (Finset.range (m + 2)).filter Q := by
    ext k; simp only [Finset.mem_filter, h]
  rw [this]

theorem card_edgePred_spine (s : Slopes (2 * (m + 1))) {e : ℕ} (h : e % 3 = 1) :
    ((Finset.range (m + 2)).filter (EdgePred m s e)).card = s.slope ((e + 2) / 3) := by
  rw [card_filter_congr _ (s.SpineMem ((e + 2) / 3)) (edgePred_spine s h),
    Slopes.card_spineMem s rfl]

theorem card_edgePred_stem (s : Slopes (2 * (m + 1))) {e : ℕ} (h : e % 3 = 2)
    (h2 : e ≠ 6 * m + 2) :
    ((Finset.range (m + 2)).filter (EdgePred m s e)).card = 2 := by
  rw [card_filter_congr _ (s.PairMem ((e + 4) / 3)) (edgePred_stem s h h2),
    Slopes.card_pairMem s rfl]

theorem card_edgePred_leaf (s : Slopes (2 * (m + 1))) {e : ℕ}
    (h : e % 3 = 0 ∨ e = 6 * m + 2) :
    ((Finset.range (m + 2)).filter (EdgePred m s e)).card = 1 := by
  rw [card_filter_congr _ (fun k => k = 0) (edgePred_leaf s h)]
  rw [show (Finset.range (m + 2)).filter (fun k => k = 0) = {0} by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    omega]
  exact Finset.card_singleton 0

theorem card_vertPred_junction (s : Slopes (2 * (m + 1))) {a : ℕ} (h : a % 3 = 2) :
    ((Finset.range (m + 2)).filter (VertPred m s a)).card
      = max (s.slope (lolli a - 1)) (s.slope (lolli a)) := by
  rw [card_filter_congr _ (s.VertMem (lolli a)) (vertPred_junction s h),
    Slopes.card_vertMem s rfl]

theorem card_vertPred_pair (s : Slopes (2 * (m + 1))) {a : ℕ} (h : a % 3 ≠ 2) :
    ((Finset.range (m + 2)).filter (VertPred m s a)).card = 2 := by
  rw [card_filter_congr _ (s.PairMem (lolli a)) (vertPred_pair s h),
    Slopes.card_pairMem s rfl]

/-! ### The junction -/

/-- The occurrence partition read at an indexed occurrence. -/
theorem ballotDatum_edgePart_occ (m : ℕ) (s : Slopes (2 * (m + 1)))
    (j : Fin (6 * m + 3)) :
    (ballotDatum m s).edgePartition (occ m j) = catStar m (EdgePred m s j.val) := by
  show ballotEdgePart m s (occ m j) = _
  rw [ballotEdgePart, edgeIndex_occ]

theorem ballotDatum_vertexPart_val (m : ℕ) (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) :
    (ballotDatum m s).vertexPartition v = catStar m (VertPred m s v.val) := rfl

/-- **Riemann--Hurwitz at a spine vertex `p_i`**, the only vertex class where
the condition has content.  The proof is the identity
`2 max (s_{i-1}, s_i) = s_{i-1} + s_i + 1`, which is the step condition. -/
theorem rh_junction_ballot (s : Slopes (2 * (m + 1))) (v : (catTree m).V)
    (hmod : v.val % 3 = 2) (hhi : v.val + 1 ≤ 6 * m) :
    (ballotDatum m s).RiemannHurwitzAtTargetVertex v := by
  intro sheet
  have hlt := v.isLt
  have hS := incidentIndices_junction m v hmod hhi
  set x : Fin (6 * m + 3) := ⟨v.val - 1, by omega⟩ with hxdef
  set y : Fin (6 * m + 3) := ⟨v.val, by omega⟩ with hydef
  set z : Fin (6 * m + 3) := ⟨v.val + 2, by omega⟩ with hzdef
  have hxv : x.val = v.val - 1 := rfl
  have hyv : y.val = v.val := rfl
  have hzv : z.val = v.val + 2 := rfl
  have hxy : x ≠ y := by intro h; rw [Fin.ext_iff, hxv, hyv] at h; omega
  have hxz : x ≠ z := by intro h; rw [Fin.ext_iff, hxv, hzv] at h; omega
  have hyz : y ≠ z := by intro h; rw [Fin.ext_iff, hyv, hzv] at h; omega
  -- the lollipop index of the junction
  have hi2 : 2 ≤ lolli v.val := by unfold lolli; omega
  have hitop : lolli v.val ≤ 2 * m + 1 := by unfold lolli; omega
  -- the three block sizes and the vertex block size
  have hMcard : ((Finset.range (m + 2)).filter (VertPred m s v.val)).card
      = max (s.slope (lolli v.val - 1)) (s.slope (lolli v.val)) :=
    card_vertPred_junction s hmod
  have hxcard : ((Finset.range (m + 2)).filter (EdgePred m s x.val)).card
      = s.slope (lolli v.val - 1) := by
    rw [hxv, card_edgePred_spine s (show (v.val - 1) % 3 = 1 by omega),
      show (v.val - 1 + 2) / 3 = lolli v.val - 1 by unfold lolli; omega]
  have hycard : ((Finset.range (m + 2)).filter (EdgePred m s y.val)).card = 2 := by
    rw [hyv]; exact card_edgePred_stem s hmod (by omega)
  have hzcard : ((Finset.range (m + 2)).filter (EdgePred m s z.val)).card
      = s.slope (lolli v.val) := by
    rw [hzv, card_edgePred_spine s (show (v.val + 2) % 3 = 1 by omega),
      show (v.val + 2 + 2) / 3 = lolli v.val by unfold lolli; omega]
  -- the step identity `2 m(B_i) = s_{i-1} + s_i + 1`
  have hstep := Slopes.slope_rel s (i := lolli v.val - 1) (by omega)
    (show (lolli v.val - 1) + 1 ≤ 2 * (m + 1) - 1 by omega)
  rw [show (lolli v.val - 1) + 1 = lolli v.val by omega] at hstep
  have hpos := Slopes.one_le_slope s (lolli v.val - 1)
  have hpos' := Slopes.one_le_slope s (lolli v.val)
  have hmax : s.slope (lolli v.val - 1) + s.slope (lolli v.val) + 1
      = 2 * max (s.slope (lolli v.val - 1)) (s.slope (lolli v.val)) := by
    rcases hstep with h | h
    · rw [max_eq_right (by omega)]; omega
    · rw [max_eq_left (by omega)]; omega
  have hle1 : s.slope (lolli v.val - 1)
      ≤ max (s.slope (lolli v.val - 1)) (s.slope (lolli v.val)) := le_max_left _ _
  have hle2 : s.slope (lolli v.val)
      ≤ max (s.slope (lolli v.val - 1)) (s.slope (lolli v.val)) := le_max_right _ _
  -- the three subset receipts
  have hsubx : ∀ k, EdgePred m s x.val k → VertPred m s v.val k := by
    intro k hk
    rw [hxv] at hk
    have hchild := edgePred_child s (m := m) (e := v.val - 1) (by omega) k hk
    rwa [show (v.val - 1) + 1 = v.val by omega] at hchild
  have hpary : parentIndex (v.val + 1) = v.val := by
    unfold parentIndex
    rw [ite_eq_right (show ¬ ((v.val + 1) % 3 = 2) by omega)]
    omega
  have hsuby : ∀ k, EdgePred m s y.val k → VertPred m s v.val k := by
    intro k hk
    rw [hyv] at hk
    have hp := edgePred_parent s (m := m) (e := v.val) (by omega) k hk
    rwa [hpary] at hp
  have hparz : parentIndex (v.val + 2 + 1) = v.val := by
    unfold parentIndex
    rw [ite_eq_left (show (v.val + 2 + 1) % 3 = 2 by omega)]
    omega
  have hsubz : ∀ k, EdgePred m s z.val k → VertPred m s v.val k := by
    intro k hk
    rw [hzv] at hk
    have hp := edgePred_parent s (m := m) (e := v.val + 2) (by omega) k hk
    rwa [hparz] at hp
  -- expand the sum
  rw [card_incidentEdges_three m v hxy hxz hyz hS,
    sum_incidentEdges_three m v hxy hxz hyz hS
      (fun e => (((ballotDatum m s).edgePartition e).blockCountWithin
        ((ballotDatum m s).vertexPartition v) sheet : ℤ)),
    ballotDatum_edgePart_occ, ballotDatum_edgePart_occ, ballotDatum_edgePart_occ,
    ballotDatum_vertexPart_val]
  by_cases hmem : VertPred m s v.val sheet.val
  · rw [catStar_blockCountWithin_of_mem _ _ (edgePred_zero s _) (vertPred_zero s _)
      hsubx hmem,
    catStar_blockCountWithin_of_mem _ _ (edgePred_zero s _) (vertPred_zero s _)
      hsuby hmem,
    catStar_blockCountWithin_of_mem _ _ (edgePred_zero s _) (vertPred_zero s _)
      hsubz hmem,
    catStar_blockCard_of_mem _ (vertPred_zero s _) hmem,
    hMcard, hxcard, hycard, hzcard]
    push_cast
    omega
  · rw [catStar_blockCountWithin_of_not _ _ (vertPred_zero s _) hmem,
      catStar_blockCountWithin_of_not _ _ (vertPred_zero s _) hmem,
      catStar_blockCountWithin_of_not _ _ (vertPred_zero s _) hmem,
      catStar_blockCard_of_not _ (vertPred_zero s _) hmem]
    norm_num

/-- **Riemann--Hurwitz for the ballot-parametrized datum, uniformly in `g` and
in the slope sequence.** -/
theorem ballotDatum_riemannHurwitz (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (ballotDatum m s).RiemannHurwitz := by
  rw [GluingDatum.riemannHurwitz_iff_forall_targetVertex]
  intro v
  have hlt := v.isLt
  rcases vertexClass m v with hv | hv | ⟨hv, hlo, hhi⟩ | hv | ⟨hv, hhi⟩ | hv
  · exact rh_valency_two _ v (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩)
      (by simp only [ne_eq, Fin.mk.injEq]; omega) (incidentIndices_root m v hv)
  · exact rh_valency_one _ v (incidentIndices_leaf m v hv)
  · exact rh_valency_two _ v (a := ⟨v.val - 1, by omega⟩) (b := ⟨v.val, by omega⟩)
      (by simp only [ne_eq, Fin.mk.injEq]; omega) (incidentIndices_stem m v hv hlo hhi)
  · exact rh_valency_one _ v (incidentIndices_lastLeaf m v hv)
  · exact rh_junction_ballot s v hv hhi
  · exact rh_valency_two _ v (a := ⟨6 * m + 1, by omega⟩) (b := ⟨6 * m + 2, by omega⟩)
      (by simp only [ne_eq, Fin.mk.injEq]; omega) (incidentIndices_lastStem m v hv)


/-! ## 5.  Connectedness

The source is covered by the `d` sheet copies of the target, and every gluing
block contains the spine sheet `0`, so connectedness amounts to: *every* label
`1 ≤ k ≤ m+1` occurs in some spine block.  That is
`Slopes.exists_cum_eq`, and the vertex where sheet `k` meets sheet `0` is the
spine vertex `p_{i+1}` in front of the spine edge `h_i` that introduced the
label. -/

/-- The copy of the target carried by one sheet. -/
def bSheetImage (m : ℕ) (s : Slopes (2 * (m + 1))) (σ : Fin (m + 2)) :
    Finset (ballotDatum m s).SourceVertex :=
  Finset.univ.image (fun v : (catTree m).V => (ballotDatum m s).sourceEndpoint v σ)

theorem connectedOn_bSheetImage (m : ℕ) (s : Slopes (2 * (m + 1))) (σ : Fin (m + 2)) :
    ConnectedOn (ballotDatum m s).sourceGraph (bSheetImage m s σ) := by
  rw [bSheetImage]
  refine connectedOn_image (source := catTree m)
    (image := (ballotDatum m s).sourceGraph)
    (fun v : (catTree m).V => (ballotDatum m s).sourceEndpoint v σ) ?_
    (catTree_connected m)
  intro a b h
  exact num_edges_sourceEndpoint_pos (ballotDatum m s) σ a b h

/-- The union of the first `k` sheet copies. -/
def bCumSheets (m : ℕ) (s : Slopes (2 * (m + 1))) (k : ℕ) :
    Finset (ballotDatum m s).SourceVertex :=
  (Finset.univ.filter fun σ : Fin (m + 2) => σ.val < k).biUnion (bSheetImage m s)

theorem bCumSheets_one (m : ℕ) (s : Slopes (2 * (m + 1))) :
    bCumSheets m s 1 = bSheetImage m s 0 := by
  have hfilter : (Finset.univ.filter fun σ : Fin (m + 2) => σ.val < 1)
      = {(0 : Fin (m + 2))} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]
    omega
  rw [bCumSheets, hfilter, Finset.singleton_biUnion]

theorem bCumSheets_succ (m : ℕ) (s : Slopes (2 * (m + 1))) {k : ℕ} (hk : k < m + 2) :
    bCumSheets m s (k + 1) = bCumSheets m s k ∪ bSheetImage m s ⟨k, hk⟩ := by
  have hfilter : (Finset.univ.filter fun σ : Fin (m + 2) => σ.val < k + 1)
      = insert (⟨k, hk⟩ : Fin (m + 2))
        (Finset.univ.filter fun σ : Fin (m + 2) => σ.val < k) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  rw [bCumSheets, hfilter, Finset.biUnion_insert, bCumSheets, Finset.union_comm]

/-- **Every sheet meets the spine sheet.**  Given a label `1 ≤ k ≤ m + 1` the
spine edge that introduced it is `h_i` with `cum s i = k` and `s_i ≥ 2`, and
the two sheets are glued at the spine vertex in front of it, numbered
`3i - 1`. -/
theorem exists_meet_spine_sheet (m : ℕ) (s : Slopes (2 * (m + 1))) {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k < m + 2) :
    ∃ w : (catTree m).V,
      (ballotDatum m s).sourceEndpoint w ⟨k, hk2⟩
        = (ballotDatum m s).sourceEndpoint w 0 := by
  have hlast : s.cum (2 * (m + 1) - 1) = m + 1 := Slopes.cum_last s rfl
  obtain ⟨i, hile, hci, hsi⟩ :=
    Slopes.exists_cum_eq s (2 * (m + 1) - 1) k hk1 (by omega)
  -- replace the index `0`, which has the same counter, by `1`
  have hone : s.cum 1 = 1 := Slopes.cum_one s
  have hslope1 : s.slope 1 = 2 := Slopes.slope_one s
  set j : ℕ := max i 1 with hj
  have hj1 : 1 ≤ j := le_max_right _ _
  have hjle : j ≤ 2 * m + 1 := by simp only [hj]; omega
  have hcj : s.cum j = k := by
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [Slopes.cum_zero] at hci
      simp only [hj]
      rw [show max 0 1 = 1 from rfl, hone, hci]
    · rw [show j = i by simp only [hj]; omega]; exact hci
  have hsj : 2 ≤ s.slope j := by
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simp only [hj]; rw [show max 0 1 = 1 from rfl, hslope1]
    · rw [show j = i by simp only [hj]; omega]; exact hsi
  have hwlt : 3 * j - 1 < 6 * m + 4 := by omega
  refine ⟨⟨3 * j - 1, hwlt⟩, ?_⟩
  refine (ballotDatum m s).sourceEndpoint_congr _ ?_
  show (catStar m (VertPred m s (3 * j - 1))).Rel ⟨k, hk2⟩ 0
  have hmod : (3 * j - 1) % 3 = 2 := by omega
  have hmem : VertPred m s (3 * j - 1) k := by
    rw [vertPred_junction s hmod]
    refine Slopes.vertMem_of_spineMem_left s ?_
    have hidx : lolli (3 * j - 1) - 1 = j := by unfold lolli; omega
    rw [hidx]
    exact Or.inr ⟨by omega, by omega⟩
  rw [catStar_rel_iff _ (vertPred_zero s _)]
  exact Or.inl ⟨hmem, vertPred_zero s _⟩

theorem connectedOn_bCumSheets (m : ℕ) (s : Slopes (2 * (m + 1))) :
    ∀ k, 1 ≤ k → k ≤ m + 2 →
      ConnectedOn (ballotDatum m s).sourceGraph (bCumSheets m s k) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hle
    by_cases hk0 : k = 0
    · subst hk0
      rw [bCumSheets_one]
      exact connectedOn_bSheetImage m s 0
    · have hk1 : 1 ≤ k := by omega
      have hklt : k < m + 2 := by omega
      obtain ⟨w, hw⟩ := exists_meet_spine_sheet m s hk1 hklt
      rw [bCumSheets_succ m s hklt]
      refine connectedOn_union (shared :=
        (ballotDatum m s).sourceEndpoint w ⟨k, hklt⟩)
        ?_ ?_ (ih hk1 (by omega)) (connectedOn_bSheetImage m s ⟨k, hklt⟩)
      · rw [hw]
        refine Finset.mem_biUnion.mpr ⟨0, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hk1
        · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem mem_bCumSheets_full (m : ℕ) (s : Slopes (2 * (m + 1)))
    (x : (ballotDatum m s).SourceVertex) : x ∈ bCumSheets m s (m + 2) := by
  rw [bCumSheets]
  refine Finset.mem_biUnion.mpr ⟨x.1.2, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.1.2.isLt
  · rw [bSheetImage]
    exact Finset.mem_image.mpr ⟨x.1.1, Finset.mem_univ _,
      (ballotDatum m s).sourceEndpoint_self x⟩

/-- **The source of the ballot-parametrized datum is connected**, uniformly in
`g` and in the slope sequence. -/
theorem ballotDatum_connected (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (ballotDatum m s).Connected :=
  graph_connected_of_connectedOn_full (bCumSheets m s (m + 2))
    (mem_bCumSheets_full m s)
    (connectedOn_bCumSheets m s (m + 2) (by omega) (le_refl _))

/-- **The ballot-parametrized caterpillar datum is a valid Draisma--Vargas
gluing datum**, for every genus and every slope sequence. -/
theorem ballotDatum_valid (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (ballotDatum m s).Valid :=
  ⟨ballotDatum_connected m s, ballotDatum_riemannHurwitz m s⟩


/-! ## 6.  The distinguished ballot sequence, and Part I's caterpillar datum

The zig-zag `(2,1,2,1,…,2)` is a slope sequence, and at it the construction
above returns Part I's `LocalCases.CaterpillarDatum.caterpillarDatum m` **on
the nose** -- not merely isomorphically.  That is the compatibility which keeps
`CaterpillarRows`, `CaterpillarSeed`, `Count.FibreCaterpillar` and everything
downstream usable from the parametrized family. -/

/-- The zig-zag list `[2,1,2,1,…,2]` of length `2n+1`. -/
def zigList : ℕ → List ℕ
  | 0 => [2]
  | (n + 1) => 2 :: 1 :: zigList n

theorem zigList_length (n : ℕ) : (zigList n).length = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => show (zigList n).length + 1 + 1 = _; rw [ih]; ring

theorem zigList_getD (n : ℕ) : ∀ j : ℕ,
    (zigList n).getD j 2 = if j ≤ 2 * n ∧ j % 2 = 1 then 1 else 2 := by
  induction n with
  | zero =>
    intro j
    rw [ite_eq_right (by omega)]
    match j with
    | 0 => rfl
    | (j + 1) => show (([] : List ℕ)).getD j 2 = 2; simp
  | succ n ih =>
    intro j
    match j with
    | 0 => rw [ite_eq_right (by omega)]; rfl
    | 1 => rw [ite_eq_left (by omega)]; rfl
    | (j + 2) =>
      show (zigList n).getD j 2 = _
      rw [ih j]
      by_cases h : j ≤ 2 * n ∧ j % 2 = 1
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem zigList_mem_one_le (n : ℕ) : ∀ x ∈ zigList n, 1 ≤ x := by
  induction n with
  | zero => intro x hx; rw [show zigList 0 = [2] from rfl] at hx; simp at hx; omega
  | succ n ih =>
    intro x hx
    rw [show zigList (n + 1) = 2 :: 1 :: zigList n from rfl, List.mem_cons,
      List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · omega
    · omega
    · exact ih x hx

theorem zigList_cons (n : ℕ) : ∃ t, zigList n = 2 :: t := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ n => exact ⟨1 :: zigList n, rfl⟩

theorem zigList_chain (n : ℕ) : List.IsChain SlopeStepRel (zigList n) := by
  induction n with
  | zero => exact List.IsChain.singleton 2
  | succ n ih =>
    obtain ⟨t, ht⟩ := zigList_cons n
    rw [show zigList (n + 1) = 2 :: 1 :: zigList n from rfl, ht]
    refine List.IsChain.cons_cons (Or.inr rfl) (List.IsChain.cons_cons (Or.inl rfl) ?_)
    rw [← ht]; exact ih

theorem zigList_head? (n : ℕ) : ∀ x ∈ (zigList n).head?, x = 2 := by
  obtain ⟨t, ht⟩ := zigList_cons n
  rw [ht]
  intro x hx
  simpa using hx.symm

theorem zigList_getLast? (n : ℕ) : ∀ x ∈ (zigList n).getLast?, x = 2 := by
  have hlen := zigList_length n
  have hlt : 2 * n + 1 - 1 < (zigList n).length := by omega
  have hval : (zigList n)[2 * n + 1 - 1] = 2 := by
    rw [List.getElem_eq_getD 2, zigList_getD]
    rw [ite_eq_right (by omega)]
  have hget : (zigList n).getLast? = some 2 := by
    rw [List.getLast?_eq_getElem?, hlen, List.getElem?_eq_getElem hlt, hval]
  rw [hget]
  intro x hx
  simpa using hx.symm

/-- **The distinguished slope sequence** `(2,1,2,1,…,2)` of genus `2m+2`: the
ballot sequence realised by Part I's caterpillar datum. -/
def zig (m : ℕ) : Slopes (2 * (m + 1)) where
  slopes := zigList m
  length_eq := by rw [zigList_length]; omega
  head_eq := zigList_head? m
  getLast_eq := zigList_getLast? m
  one_le := zigList_mem_one_le m
  step := zigList_chain m

theorem zig_slope (m i : ℕ) :
    (zig m).slope i = if 1 ≤ i ∧ i ≤ 2 * m + 1 ∧ i % 2 = 0 then 1 else 2 := by
  show (zigList m).getD (i - 1) 2 = _
  rw [zigList_getD]
  by_cases h : 1 ≤ i ∧ i ≤ 2 * m + 1 ∧ i % 2 = 0
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem zig_slope_mid (m : ℕ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 2 * m + 1) :
    (zig m).slope i = if i % 2 = 0 then 1 else 2 := by
  rw [zig_slope]
  by_cases h : i % 2 = 0
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

theorem zig_cum (m : ℕ) : ∀ i : ℕ, 1 ≤ i → i ≤ 2 * m + 2 →
    (zig m).cum i = (i + 1) / 2 := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [Slopes.cum_one]
    · rcases Nat.lt_or_ge i (2 * m + 1) with hlt | hge
      · have hprev := ih hipos (by omega)
        rw [Slopes.cum_succ, hprev,
          zig_slope_mid m (i := i + 1) (by omega) (by omega),
          zig_slope_mid m (i := i) (by omega) (by omega)]
        by_cases hpar : i % 2 = 0
        · rw [ite_eq_left hpar, ite_eq_right (show ¬ ((i + 1) % 2 = 0) by omega),
            ite_eq_left (by omega)]
          omega
        · rw [ite_eq_right hpar, ite_eq_left (show (i + 1) % 2 = 0 by omega),
            ite_eq_right (by omega)]
          omega
      · have hstop : (zig m).cum (i + 1) = (zig m).cum i :=
          Slopes.cum_of_ge (zig m) (by omega)
        have hi : i = 2 * m + 1 := by omega
        subst hi
        rw [hstop, ih (by omega) (by omega)]
        omega

/-! ### The three predicates at the zig-zag -/

theorem zig_spineMem (m : ℕ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 2 * m + 1) (k : ℕ) :
    (zig m).SpineMem i k ↔ (if i % 2 = 1 then (k = 0 ∨ k = (i + 1) / 2) else k = 0) := by
  have hc := zig_cum m i h1 (by omega)
  have hs := zig_slope_mid m h1 h2
  unfold Slopes.SpineMem
  rw [hc]
  by_cases hpar : i % 2 = 1
  · rw [ite_eq_right (show ¬ (i % 2 = 0) by omega)] at hs
    rw [hs, ite_eq_left hpar]
    omega
  · rw [ite_eq_left (show i % 2 = 0 by omega)] at hs
    rw [hs, ite_eq_right hpar]
    omega

theorem zig_vertMem (m : ℕ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 2 * m + 2) (k : ℕ) :
    (zig m).VertMem i k ↔ (k = 0 ∨ k = (i + 1) / 2) := by
  unfold Slopes.VertMem
  rcases Nat.lt_or_ge i (2 * m + 2) with hlt | hge
  · rcases Nat.eq_or_lt_of_le h1 with hone | hbig
    · -- `i = 1`: both neighbours are the block `{0,1}`
      subst hone
      rw [zig_spineMem m (i := 1) (by omega) (by omega),
        ite_eq_left (by omega)]
      have h0 : (zig m).SpineMem 0 k ↔ (k = 0 ∨ k = 1) := by
        unfold Slopes.SpineMem
        rw [Slopes.cum_zero, show (zig m).slope 0 = 2 by
          rw [zig_slope, ite_eq_right (by omega)]]
        omega
      rw [show (1 : ℕ) - 1 = 0 from rfl, h0]
      norm_num
    · by_cases hpar : i % 2 = 1
      · rw [zig_spineMem m (i := i) (by omega) (by omega),
          zig_spineMem m (i := i - 1) (by omega) (by omega),
          ite_eq_left hpar, ite_eq_right (by omega)]
        omega
      · rw [zig_spineMem m (i := i) (by omega) (by omega),
          zig_spineMem m (i := i - 1) (by omega) (by omega),
          ite_eq_right hpar, ite_eq_left (by omega)]
        have : (i - 1 + 1) / 2 = (i + 1) / 2 := by omega
        rw [this]
        omega
  · -- `i = 2m+2`: the last lollipop, where both neighbours are `{0, m+1}`
    have hi : i = 2 * m + 2 := by omega
    subst hi
    rw [zig_spineMem m (i := 2 * m + 2 - 1) (by omega) (by omega),
      ite_eq_left (by omega)]
    have htop : (zig m).SpineMem (2 * m + 2) k ↔ (k = 0 ∨ k = m + 1) := by
      unfold Slopes.SpineMem
      rw [zig_cum m (2 * m + 2) (by omega) (by omega),
        show (zig m).slope (2 * m + 2) = 2 by rw [zig_slope, ite_eq_right (by omega)]]
      omega
    rw [htop]
    have : (2 * m + 2 - 1 + 1) / 2 = m + 1 := by omega
    rw [this]
    omega

theorem zig_pairMem (m : ℕ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 2 * m + 2) (k : ℕ) :
    (zig m).PairMem i k ↔ (k = 0 ∨ k = (i + 1) / 2) := by
  unfold Slopes.PairMem
  rw [zig_cum m i h1 h2]

/-! ### The two partitions agree with Part I's -/

theorem zig_vertPred (m : ℕ) {a : ℕ} (ha : a ≤ 6 * m + 3) (k : ℕ) :
    VertPred m (zig m) a k ↔ (k = 0 ∨ k = pairIndex a) := by
  have hl1 : 1 ≤ lolli a := lolli_pos a
  have hl2 : lolli a ≤ 2 * m + 2 := lolli_le m a ha
  have hpi : pairIndex a = (lolli a + 1) / 2 := rfl
  by_cases h : a % 3 = 2
  · rw [vertPred_junction (zig m) h, zig_vertMem m hl1 hl2, hpi]
  · rw [vertPred_pair (zig m) h, zig_pairMem m hl1 hl2, hpi]

theorem zig_edgePred (m : ℕ) {e : ℕ} (he : e ≤ 6 * m + 2) (k : ℕ) :
    EdgePred m (zig m) e k ↔
      (if IsPairEdge m e then (k = 0 ∨ k = pairIndex (e + 1)) else k = 0) := by
  have hpi : pairIndex (e + 1) = (lolli (e + 1) + 1) / 2 := rfl
  have hlol : lolli (e + 1) = (e + 5) / 3 := rfl
  by_cases hspine : e % 3 = 1
  · rw [edgePred_spine (zig m) hspine,
      zig_spineMem m (i := (e + 2) / 3) (by omega) (by omega)]
    by_cases hodd : ((e + 2) / 3) % 2 = 1
    · rw [ite_eq_left hodd, ite_eq_left (show IsPairEdge m e by unfold IsPairEdge; omega),
        hpi, hlol]
      have : ((e + 2) / 3 + 1) / 2 = ((e + 5) / 3 + 1) / 2 := by omega
      rw [this]
    · rw [ite_eq_right hodd, ite_eq_right (show ¬ IsPairEdge m e by unfold IsPairEdge; omega)]
  · by_cases hstem : e % 3 = 2 ∧ e ≠ 6 * m + 2
    · rw [edgePred_stem (zig m) hstem.1 hstem.2,
        zig_pairMem m (i := (e + 4) / 3) (by omega) (by omega),
        ite_eq_left (show IsPairEdge m e by unfold IsPairEdge; exact Or.inr hstem),
        hpi, hlol]
      have : ((e + 4) / 3 + 1) / 2 = ((e + 5) / 3 + 1) / 2 := by omega
      rw [this]
    · rw [edgePred_leaf (zig m) (by omega),
        ite_eq_right (show ¬ IsPairEdge m e by unfold IsPairEdge; omega)]

/-- **The vertex partitions agree.** -/
theorem ballotVertexPart_zig (m : ℕ) (v : (catTree m).V) :
    ballotVertexPart m (zig m) v = catVertexPart m v := by
  have hlt := v.isLt
  rw [ballotVertexPart, catVertexPart]
  exact catStar_eq_pairPart _ _ (zig_vertPred m (by omega))

/-- **The occurrence partitions agree.** -/
theorem ballotEdgePart_zig (m : ℕ) (e : (catTree m).edges) :
    ballotEdgePart m (zig m) e = catEdgePart m e := by
  obtain ⟨i, rfl⟩ := occ_surj m e
  have hi := i.isLt
  rw [ballotEdgePart, edgeIndex_occ, catEdgePart, edgeIndex_occ]
  by_cases hpair : IsPairEdge m i.val
  · rw [ite_eq_left hpair]
    refine catStar_eq_pairPart _ _ (fun k => ?_)
    rw [zig_edgePred m (by omega), ite_eq_left hpair]
  · rw [ite_eq_right hpair]
    refine catStar_eq_discrete _ (fun k => ?_)
    rw [zig_edgePred m (by omega), ite_eq_right hpair]

/-- **The reduction.**  At the distinguished ballot sequence the
ballot-parametrized datum *is* Part I's caterpillar datum -- an equality of
gluing data, not an isomorphism. -/
theorem ballotDatum_zig (m : ℕ) : ballotDatum m (zig m) = caterpillarDatum m := by
  refine gluingDatum_ext ?_ ?_
  · funext v; exact ballotVertexPart_zig m v
  · funext e; exact ballotEdgePart_zig m e


/-! ## 7.  The grafting census at a spine vertex

Part II describes the source over a spine vertex `p_i` as the bridge together
with `m(B_i) - 2` grafted length-two dangling paths, oriented by the sign of
`s_i - s_{i-1} = ±1`.  In the quotient-source encoding both halves of that
description are readable off `blockCountWithin`, and they are two **different**
statements, which is worth recording because Part II states them together:

* over the **stem** the block `V_i` of `m(B_i)` sheets splits as one pair (the
  bridge, index two) and `m(B_i) - 2` singletons, each of which continues over
  the leaf edge as the second half of a length-two dangling path
  (`stem_blockCount`);
* over the **two spine edges** it splits as the spine block `S_{i∓1}` and
  `m(B_i) - s_{i∓1}` singletons, and those two deficits sum to exactly **one**
  (`spine_blockCount_back`, `spine_blockCount_forward`,
  `spine_dangling_total`).  So besides the `m(B_i) - 2` lollipop paths there is
  exactly one further index-one edge at `B_i`, lying over the spine edge on the
  *lower* side of the step -- and that, not the lollipop paths, is what the
  sign of `s_i - s_{i-1}` orients.

Both are forced: harmonicity at `B_i` needs `m(B_i)` in every direction, and
`s_{i-1} + s_i = 2 m(B_i) - 1` leaves a deficit of one on exactly one spine
side. -/

section Census

variable (s : Slopes (2 * (m + 1))) (v : (catTree m).V)
  (hmod : v.val % 3 = 2) (hhi : v.val + 1 ≤ 6 * m) (σ : Fin (m + 2))

/-- **Over the stem: one bridge and `m(B_i) - 2` grafted dangling paths.** -/
theorem stem_blockCount (hσ : VertPred m s v.val σ.val) :
    ((ballotDatum m s).edgePartition
        (occ m ⟨v.val, show v.val < 6 * m + 3 by omega⟩)).blockCountWithin
      ((ballotDatum m s).vertexPartition v) σ
      = 1 + (max (s.slope (lolli v.val - 1)) (s.slope (lolli v.val)) - 2) := by
  have hpary : parentIndex (v.val + 1) = v.val := by
    unfold parentIndex
    rw [ite_eq_right (show ¬ ((v.val + 1) % 3 = 2) by omega)]
    omega
  have hsub : ∀ k, EdgePred m s v.val k → VertPred m s v.val k := by
    intro k hk
    have hp := edgePred_parent s (m := m) (e := v.val) (by omega) k hk
    rwa [hpary] at hp
  rw [ballotDatum_edgePart_occ, ballotDatum_vertexPart_val,
    catStar_blockCountWithin_of_mem _ _ (edgePred_zero s _) (vertPred_zero s _)
      hsub hσ,
    card_vertPred_junction s hmod, card_edgePred_stem s hmod (by omega)]

/-- **Over the backward spine edge `h_{i-1}`.** -/
theorem spine_blockCount_back (hσ : VertPred m s v.val σ.val) :
    ((ballotDatum m s).edgePartition
        (occ m ⟨v.val - 1, show v.val - 1 < 6 * m + 3 by omega⟩)).blockCountWithin
      ((ballotDatum m s).vertexPartition v) σ
      = 1 + (max (s.slope (lolli v.val - 1)) (s.slope (lolli v.val))
          - s.slope (lolli v.val - 1)) := by
  have hsub : ∀ k, EdgePred m s (v.val - 1) k → VertPred m s v.val k := by
    intro k hk
    have hchild := edgePred_child s (m := m) (e := v.val - 1) (by omega) k hk
    rwa [show (v.val - 1) + 1 = v.val by omega] at hchild
  rw [ballotDatum_edgePart_occ, ballotDatum_vertexPart_val,
    catStar_blockCountWithin_of_mem _ _ (edgePred_zero s _) (vertPred_zero s _)
      hsub hσ,
    card_vertPred_junction s hmod,
    card_edgePred_spine s (show (v.val - 1) % 3 = 1 by omega),
    show (v.val - 1 + 2) / 3 = lolli v.val - 1 by unfold lolli; omega]

/-- **Over the forward spine edge `h_i`.** -/
theorem spine_blockCount_forward (hσ : VertPred m s v.val σ.val) :
    ((ballotDatum m s).edgePartition
        (occ m ⟨v.val + 2, show v.val + 2 < 6 * m + 3 by omega⟩)).blockCountWithin
      ((ballotDatum m s).vertexPartition v) σ
      = 1 + (max (s.slope (lolli v.val - 1)) (s.slope (lolli v.val))
          - s.slope (lolli v.val)) := by
  have hparz : parentIndex (v.val + 2 + 1) = v.val := by
    unfold parentIndex
    rw [ite_eq_left (show (v.val + 2 + 1) % 3 = 2 by omega)]
    omega
  have hsub : ∀ k, EdgePred m s (v.val + 2) k → VertPred m s v.val k := by
    intro k hk
    have hp := edgePred_parent s (m := m) (e := v.val + 2) (by omega) k hk
    rwa [hparz] at hp
  rw [ballotDatum_edgePart_occ, ballotDatum_vertexPart_val,
    catStar_blockCountWithin_of_mem _ _ (edgePred_zero s _) (vertPred_zero s _)
      hsub hσ,
    card_vertPred_junction s hmod,
    card_edgePred_spine s (show (v.val + 2) % 3 = 1 by omega),
    show (v.val + 2 + 2) / 3 = lolli v.val by unfold lolli; omega]

end Census

/-- **The orientation.**  The two spine deficits sum to exactly one: besides the
`m(B_i) - 2` length-two paths into the lollipop there is exactly one further
index-one edge at `B_i`, and it lies over the spine edge on the lower side of
the step `s_i - s_{i-1} = ±1`. -/
theorem spine_dangling_total (m : ℕ) (s : Slopes (2 * (m + 1))) (v : (catTree m).V)
    (hmod : v.val % 3 = 2) (hhi : v.val + 1 ≤ 6 * m) :
    (max (s.slope (lolli v.val - 1)) (s.slope (lolli v.val))
        - s.slope (lolli v.val - 1))
      + (max (s.slope (lolli v.val - 1)) (s.slope (lolli v.val))
        - s.slope (lolli v.val)) = 1 := by
  have hlt := v.isLt
  have hi2 : 2 ≤ lolli v.val := by unfold lolli; omega
  have hitop : lolli v.val ≤ 2 * m + 1 := by unfold lolli; omega
  have hstep : SlopeStepRel (s.slope (lolli v.val - 1)) (s.slope (lolli v.val)) := by
    have h := Slopes.slope_rel s (i := lolli v.val - 1) (by omega)
      (show (lolli v.val - 1) + 1 ≤ 2 * (m + 1) - 1 by omega)
    rwa [show (lolli v.val - 1) + 1 = lolli v.val by omega] at h
  rcases hstep with h | h
  · rw [max_eq_right (by omega)]; omega
  · rw [max_eq_left (by omega)]; omega



/-! ## 8.  Non-vacuity, and consistency with Part I's datum

The family is indexed by a type that is really populated: at genus six there
are `Slopes.card_six_eq_five = 5` slope sequences, and `Slopes.six`
(`[2,3,4,3,2]`) is one of them that is **not** the zig-zag, so the datum below
is a genuinely new object, not a repackaging of `caterpillarDatum 2`. -/

/-- Genus six, degree four: a gluing datum for every one of the five ballot
sequences. -/
example (s : Slopes 6) : GluingDatum (catTree 2) 4 := ballotDatum 2 s

/-- …and every one of them is valid. -/
example (s : Slopes 6) : (ballotDatum 2 s).Valid := ballotDatum_valid 2 s

/-- The rise-then-fall sequence `[2,3,4,3,2]` gives a valid datum whose spine
blocks really grow to four sheets. -/
example : (ballotDatum 2 Slopes.six).Valid := ballotDatum_valid 2 Slopes.six

/-- It is not the zig-zag: `Slopes.six` has `s_2 = 3`, the zig-zag has
`s_2 = 1`. -/
example : (Slopes.six).slope 2 = 3 := rfl

example : (zig 2).slope 2 = 1 := rfl

/-- **Consistency.**  Part I's validity theorem for the caterpillar datum is the
specialisation of the parametrized one at the distinguished ballot sequence. -/
example (m : ℕ) : (caterpillarDatum m).Valid := by
  rw [← ballotDatum_zig m]
  exact ballotDatum_valid m (zig m)

end DraismaVargas.Count.BallotDatum
