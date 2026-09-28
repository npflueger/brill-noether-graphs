import DraismaVargasCount.SheetLayerCensus
import DraismaVargasCount.PartitionCensusProof
import DraismaVargasCount.TargetGeodesic
import DraismaVargas.LocalCases.DanglingSideStructure
import DraismaVargas.LocalCases.CaterpillarDatum
import DraismaVargas.LocalCases.CaterpillarPruning


/-!
# The datum supply `hSupply`, half B: the global matching

The second half of the datum-supply hypothesis `hSupply` (two open odd diagonal members of
the caterpillar fibre with the same core diagonal have isomorphic gluing data), and with it
`hSupply` itself.  Builds on `Count/DiagonalTargetIso.lean` (Half 1's target layer,
`SheetLayer`, `SheetLayerSupply`, `hSupply_of_sheetLayerSupply`),
`Count/SheetLayerCensus.lean` and `Count/PartitionCensusProof.lean` (the census and its
proof), `TrivalentFibreUnique.fibreVertexUnique`, `Count/LeafFibre.lean` and the
dangling-side confinement of `LocalCases/DanglingSideStructure.lean`.

## What is proved

**The obligation, at every `m`.**
`sheetLayerSupply_of_partitionCensus : PartitionCensus m request → SheetLayerSupply m request`.
With `PartitionCensusProof.partitionCensus` this gives `SheetLayerSupply`
**outright** (`sheetLayerSupply`), and more generally a sheet layer over Half 1's target
layer between *any* two diagonal members with equal core diagonals
(`sheetLayer_of_coreDiag_eq`, which the base count `CaterpillarAllMembers` consumes).  Hence
`hSupply_of_partitionCensus` (in the binder shape of `hSupply`) and
**`hSupply_genusSix`** (no hypotheses).

**The route.**
* §1--§2 (generic).  Permutations of `Fin d` with prescribed labels
  (`exists_perm_of_card_fiber`, `exists_perm_on`); rooted trees from
  `TargetGeodesic.TreeRank`: roots, ancestors (`AncEq`), a connected target has one root
  above everything (`exists_root`), and walks avoiding a vertex (`AvoidStep`,
  `walk_up`, `walk_down`, `ancEq_of_walk`).
* §3--§6, **the abstract matching theorem** `exists_sheetPerms`.  Two *star data* over
  one rooted tree -- every vertex partition is one anchor block plus singletons, every
  occurrence partition is either discrete or "the sheets in both end anchors, plus
  singletons" (the same kind on both sides) -- whose anchors are **ancestor-convex**
  (`Convex`: a sheet that leaves the anchor on the way up from `x` never re-enters it
  outside the subtree of `x`) and have equal sizes at every vertex and over every
  occurrence, are related by vertex and occurrence permutations compatible along every
  occurrence.  The construction (`vertexPerm`, `edgePerm`): at the root a permutation
  preserving the **top** of every sheet's anchor region (`label`, `rootPerm`); at
  `high e` the permutation at `low e` corrected on the anchor at `low e` only
  (`kappaOf`, carrying `A_low ∩ A_high` onto the sheets sent into the second
  `A_high`); then a swap inside the anchor fixing the representative (`fixAt`); over
  `e` the corrected base followed by a swap inside `A_low ∩ A_high` (`edgeFix`).  The
  invariants (`Inv`: anchors matched, and the top label of every non-ancestor
  preserved) go down the tree by strong induction on the rank (`inv_vertexPerm`).
* §7, **every diagonal member is a convex star datum.**  `anchorVertex` is the unique
  surviving source vertex over each target vertex (`TrivalentFibreUnique`); vertex
  partitions are stars around it (`SheetLayerCensus`, and Observation I in Part I's proof
  of `lemma-dangling-no-glue`); `edge_rel_iff`: over a non-leaf slot's edge the one
  surviving occurrence is the block `A_u ∩ A_w` (a dangling occurrence joining the two
  anchors would be parallel to it, `CaterpillarPruning.not_isDangling_of_parallel`),
  over a loop slot's edge the partition is discrete; `convex_walk`: if `σ` is in the
  anchor at `x` but not at its neighbour `z`, the occurrence of `σ` over `xz` is
  dangling (its end over `z` does not survive), its genus-zero side is the one
  containing `z` (the other end survives), and by confinement
  (`DanglingSideStructure.mem_side_of_reachP`) that side contains every vertex that a
  walk from `z` avoiding `x` reaches on sheet `σ` -- none of which survives, so none is
  an anchor.  `card_both_of_not_kind`: over a loop slot's edge the two end anchors share
  exactly the two sheets of the tip's anchor.
* §8--§9.  The census gives the anchor sizes (`star_card_eq`: two stars related by a
  relabelling have anchors of the same size), and `sheetLayer_of_census` assembles the
  abstract theorem over Half 1's target layer.
* §11, **the root permutation is not free**: `root_choice_not_free` -- over the
  three-vertex path, at a valid star datum, the swap of two sheets realises the census
  at the (discrete) middle vertex but is the middle permutation of no sheet layer of
  the datum with itself.  What makes the induction go through is label preservation at
  the root, which needs convexity.

## What is not proved here

* Nothing is left open on `hSupply`: `hSupply_genusSix` has no hypotheses.
* `Open` and `HasOddMult` are carried by `SheetLayerSupply` but unused: the matching
  holds between any two diagonal members with equal core diagonals.
* Source connectedness is **not** what makes the matching work, and it is not used.  Over
  the path `a - b - c` at degree four, the data with `{0,1} {2,3}` over `b`, one block over
  `a` and over `c`, `{0,1} {2} {3}` over `ab`, and either `{2,3} {0} {1}` or
  `{0,1} {2} {3}` over `bc` have connected sources and matching censuses but are not
  isomorphic (in the first both blocks over `b` carry one doubled and one split
  occurrence, in the second one block carries both doubled ones).  This remark is not
  formalised; the operative hypotheses are the star shape and convexity, both proved in §7
  for diagonal members.
-/
namespace DraismaVargas.Count.SheetLayerMatching

open DraismaVargas.Infrastructure
open DraismaVargas.Count.TargetGeodesic
open Finset

section Perm

variable {d : ℕ}

theorem exists_perm_of_card_fiber {γ : Type*} [Fintype γ] [DecidableEq γ]
    (f g : Fin d → γ)
    (h : ∀ c, (univ.filter fun σ ↦ f σ = c).card = (univ.filter fun σ ↦ g σ = c).card) :
    ∃ ρ : Equiv.Perm (Fin d), ∀ σ, g (ρ σ) = f σ := by
  classical
  refine ⟨Equiv.ofFiberEquiv (fun c ↦ Fintype.equivOfCardEq ?_),
    fun σ ↦ Equiv.ofFiberEquiv_map _ σ⟩
  rw [Fintype.card_subtype, Fintype.card_subtype]
  exact h c

theorem card_filter_and_not (U X : Fin d → Prop) [DecidablePred U] [DecidablePred X]
    (hX : ∀ σ, X σ → U σ) :
    (univ.filter fun σ ↦ U σ ∧ ¬ X σ).card + (univ.filter X).card = (univ.filter U).card := by
  classical
  have h := card_filter_add_card_filter_not (s := univ.filter U) X
  rw [filter_filter, filter_filter] at h
  have e : (univ.filter fun σ ↦ U σ ∧ X σ) = univ.filter X := by
    ext σ; simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hX σ h, h⟩⟩
  rw [e] at h
  omega

/-- **A permutation supported on `U` carrying `X` onto `Y`.** -/
theorem exists_perm_on (U X Y : Fin d → Prop) [DecidablePred U] [DecidablePred X]
    [DecidablePred Y] (hX : ∀ σ, X σ → U σ) (hY : ∀ σ, Y σ → U σ)
    (h : (univ.filter X).card = (univ.filter Y).card) :
    ∃ κ : Equiv.Perm (Fin d), (∀ σ, ¬ U σ → κ σ = σ) ∧
      (∀ σ, U σ → U (κ σ) ∧ (Y (κ σ) ↔ X σ)) := by
  classical
  let f : Fin d → Bool ⊕ Fin d := fun σ ↦ if U σ then Sum.inl (decide (X σ)) else Sum.inr σ
  let g : Fin d → Bool ⊕ Fin d := fun σ ↦ if U σ then Sum.inl (decide (Y σ)) else Sum.inr σ
  have hcard : ∀ c, (univ.filter fun σ ↦ f σ = c).card =
      (univ.filter fun σ ↦ g σ = c).card := by
    intro c
    rcases c with b | τ
    · cases b
      · have e1 : (univ.filter fun σ ↦ f σ = Sum.inl false) =
            univ.filter (fun σ ↦ U σ ∧ ¬ X σ) := by
          ext σ; simp only [mem_filter, mem_univ, true_and, f]
          split_ifs with hU <;> simp [hU]
        have e2 : (univ.filter fun σ ↦ g σ = Sum.inl false) =
            univ.filter (fun σ ↦ U σ ∧ ¬ Y σ) := by
          ext σ; simp only [mem_filter, mem_univ, true_and, g]
          split_ifs with hU <;> simp [hU]
        rw [e1, e2]
        have k1 := card_filter_and_not U X hX
        have k2 := card_filter_and_not U Y hY
        omega
      · have e1 : (univ.filter fun σ ↦ f σ = Sum.inl true) = univ.filter X := by
          ext σ; simp only [mem_filter, mem_univ, true_and, f]
          split_ifs with hU
          · simp
          · simp only [false_iff]
            exact fun hx ↦ hU (hX σ hx)
        have e2 : (univ.filter fun σ ↦ g σ = Sum.inl true) = univ.filter Y := by
          ext σ; simp only [mem_filter, mem_univ, true_and, g]
          split_ifs with hU
          · simp
          · simp only [false_iff]
            exact fun hy ↦ hU (hY σ hy)
        rw [e1, e2, h]
    · have e1 : (univ.filter fun σ ↦ f σ = Sum.inr τ) =
          univ.filter (fun σ ↦ ¬ U σ ∧ σ = τ) := by
        ext σ; simp only [mem_filter, mem_univ, true_and, f]
        split_ifs with hU <;> simp [hU]
      have e2 : (univ.filter fun σ ↦ g σ = Sum.inr τ) =
          univ.filter (fun σ ↦ ¬ U σ ∧ σ = τ) := by
        ext σ; simp only [mem_filter, mem_univ, true_and, g]
        split_ifs with hU <;> simp [hU]
      rw [e1, e2]
  obtain ⟨κ, hκ⟩ := exists_perm_of_card_fiber f g hcard
  refine ⟨κ, fun σ hσ ↦ ?_, fun σ hσ ↦ ?_⟩
  · have hk := hκ σ
    simp only [f, g, if_neg hσ] at hk
    split_ifs at hk with h'
    exact Sum.inr.inj hk
  · have hk := hκ σ
    simp only [f, g, if_pos hσ] at hk
    split_ifs at hk with h'
    refine ⟨h', ?_⟩
    simpa using Sum.inl.inj hk

/-- Precomposing a filter predicate with a permutation does not change the count. -/
theorem card_filter_comp_perm (p : Equiv.Perm (Fin d)) (Q : Fin d → Prop) [DecidablePred Q] :
    (univ.filter fun σ ↦ Q (p σ)).card = (univ.filter Q).card := by
  classical
  refine Finset.card_bij (fun σ _ ↦ p σ) ?_ ?_ ?_
  · intro σ hσ
    simpa using hσ
  · intro a _ b _ hab
    exact p.injective hab
  · intro τ hτ
    refine ⟨p.symm τ, by simpa using hτ, by simp⟩

/-- A transposition of two members of `S` preserves `S` and fixes its complement. -/
theorem swap_mem_iff (S : Fin d → Prop) {a b : Fin d} (ha : S a) (hb : S b) (σ : Fin d) :
    S (Equiv.swap a b σ) ↔ S σ := by
  by_cases h1 : σ = a
  · subst h1; rw [Equiv.swap_apply_left]; exact ⟨fun _ ↦ ha, fun _ ↦ hb⟩
  by_cases h2 : σ = b
  · subst h2; rw [Equiv.swap_apply_right]; exact ⟨fun _ ↦ hb, fun _ ↦ ha⟩
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem swap_apply_of_not (S : Fin d → Prop) {a b : Fin d} (ha : S a) (hb : S b) {σ : Fin d}
    (hσ : ¬ S σ) : Equiv.swap a b σ = σ :=
  Equiv.swap_apply_of_ne_of_ne (fun h ↦ hσ (h ▸ ha)) (fun h ↦ hσ (h ▸ hb))

end Perm
/-! ## 2. Rooted trees: ancestors, the root, and walks -/

section Tree

variable {T : CFGraph.{0}} (R : TreeRank T)

/-- A root: the larger end of no occurrence. -/
def IsRoot (v : T.V) : Prop := ∀ e : T.edges, R.high e ≠ v

/-- `x` is `v` or an ancestor of `v`. -/
def AncEq (x v : T.V) : Prop := ∃ k : ℕ, R.up^[k] v = x

theorem ancEq_refl (x : T.V) : AncEq R x x := ⟨0, rfl⟩

theorem up_eq_self_of_isRoot {v : T.V} (h : IsRoot R v) : R.up v = v := by
  unfold TreeRank.up
  rw [dif_neg (by rintro ⟨e, he⟩; exact h e he)]

theorem exists_high_of_not_isRoot {v : T.V} (h : ¬ IsRoot R v) : ∃ e, R.high e = v := by
  by_contra hNo
  exact h fun e he ↦ hNo ⟨e, he⟩

theorem iterate_up_of_isRoot {v : T.V} (h : IsRoot R v) (k : ℕ) : R.up^[k] v = v :=
  Function.iterate_fixed (up_eq_self_of_isRoot R h) k

theorem rank_up_lt_of_not_isRoot {v : T.V} (h : ¬ IsRoot R v) : R.rank (R.up v) < R.rank v := by
  obtain ⟨e, rfl⟩ := exists_high_of_not_isRoot R h
  rw [R.up_high]
  exact R.rank_low_lt e

theorem isRoot_of_rank_eq_zero {v : T.V} (h : R.rank v = 0) : IsRoot R v := by
  intro e he
  have := R.rank_low_lt e
  rw [he, h] at this
  omega

theorem isRoot_iterate_up : ∀ (n : ℕ) (v : T.V), R.rank v ≤ n → IsRoot R (R.up^[n] v)
  | 0, v, h => by show IsRoot R v; exact isRoot_of_rank_eq_zero R (by omega)
  | n + 1, v, h => by
    by_cases hv : IsRoot R v
    · rw [iterate_up_of_isRoot R hv]; exact hv
    · rw [Function.iterate_succ_apply]
      exact isRoot_iterate_up n _ (by have := rank_up_lt_of_not_isRoot R hv; omega)

theorem iterate_up_eq_self_of_rank : ∀ (k : ℕ) (v : T.V),
    R.rank (R.up^[k] v) = R.rank v → R.up^[k] v = v
  | 0, v, _ => rfl
  | k + 1, v, h => by
    rw [Function.iterate_succ_apply] at h ⊢
    have h1 := R.rank_iterate_up_le k (R.up v)
    have h2 := R.rank_up_le v
    have hv : IsRoot R v := by
      by_contra hv
      have := rank_up_lt_of_not_isRoot R hv
      omega
    rw [up_eq_self_of_isRoot R hv] at h ⊢
    exact iterate_up_eq_self_of_rank k v h

theorem ancEq_antisymm {x v : T.V} (h₁ : AncEq R x v) (h₂ : AncEq R v x) : x = v := by
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  have a := R.rank_iterate_up_le k v
  have b := R.rank_iterate_up_le j x
  rw [hk] at a
  rw [hj] at b
  have hEq : R.rank (R.up^[k] v) = R.rank v := by rw [hk]; omega
  rw [← hk]
  exact iterate_up_eq_self_of_rank R k v hEq

theorem not_ancEq_high_low (e : T.edges) : ¬ AncEq R (R.high e) (R.low e) := by
  rintro ⟨k, hk⟩
  have a := R.rank_iterate_up_le k (R.low e)
  rw [hk] at a
  have := R.rank_low_lt e
  omega

theorem ancEq_high_of_ancEq_low {x : T.V} (e : T.edges) (h : AncEq R x (R.low e)) :
    AncEq R x (R.high e) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [Function.iterate_succ_apply, R.up_high]; exact hk⟩

theorem ancEq_root_high_iff {r : T.V} (hr : IsRoot R r) (e : T.edges) :
    AncEq R r (R.high e) ↔ AncEq R r (R.low e) := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact absurd hk (hr e)
    | succ k =>
      rw [Function.iterate_succ_apply, R.up_high] at hk
      exact ⟨k, hk⟩
  · exact ancEq_high_of_ancEq_low R e

/-- The single edge-cut form of connectedness gives an edge from a positive
multiplicity. -/
theorem exists_edge_of_num_edges_pos {a b : T.V} (h : 0 < num_edges T a b) :
    ∃ g : T.edges, (g : T.V × T.V) = (a, b) ∨ (g : T.V × T.V) = (b, a) := by
  obtain ⟨pair, hPair, hEnds⟩ :=
    Infrastructure.GraphContraction.exists_mem_edges_of_num_edges_pos T _ _ h
  exact ⟨⟨pair, ⟨0, Multiset.count_pos.mpr hPair⟩⟩, hEnds⟩

/-- **A connected target has one root, and it is an ancestor of every vertex.** -/
theorem exists_root (hConn : graph_connected T) :
    ∃ r : T.V, IsRoot R r ∧ ∀ v, AncEq R r v := by
  classical
  obtain ⟨v₀⟩ := T.instNonempty
  set r := R.up^[R.rank v₀] v₀ with hr
  have hRoot : IsRoot R r := isRoot_iterate_up R _ _ le_rfl
  refine ⟨r, hRoot, ?_⟩
  by_contra hNot
  push Not at hNot
  obtain ⟨w, hw⟩ := hNot
  obtain ⟨a, ha, b, hb, hab⟩ := hConn (univ.filter fun v ↦ AncEq R r v)
    ⟨v₀, w, by simpa using ⟨R.rank v₀, hr.symm⟩, by simpa using hw⟩
  simp only [mem_filter, mem_univ, true_and] at ha hb
  obtain ⟨g, hg⟩ := exists_edge_of_num_edges_pos (T := T) hab
  have hIff := ancEq_root_high_iff R hRoot g
  rcases R.ends g with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hg with hg | hg <;>
    rw [hg] at h1 h2 <;> simp only at h1 h2 <;> rw [← h1, ← h2] at hIff <;> tauto

/-! ### Walks avoiding a vertex -/

/-- Two target vertices joined by an occurrence. -/
def Adj (u u' : T.V) : Prop :=
  ∃ g : T.edges, ((g : T.V × T.V).1 = u ∧ (g : T.V × T.V).2 = u') ∨
    ((g : T.V × T.V).1 = u' ∧ (g : T.V × T.V).2 = u)

/-- One step of a walk that never enters `x`. -/
def AvoidStep (x u u' : T.V) : Prop := Adj u u' ∧ u' ≠ x

theorem adj_low_high (e : T.edges) : Adj (R.low e) (R.high e) := by
  rcases R.ends e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨e, Or.inl ⟨h1, h2⟩⟩
  · exact ⟨e, Or.inr ⟨h1, h2⟩⟩

theorem adj_symm {u u' : T.V} (h : Adj u u') : Adj u' u := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg.symm⟩

/-- Climbing from `v` never enters a vertex of larger rank. -/
theorem walk_up {x v : T.V} (hv : R.rank v < R.rank x) :
    ∀ j : ℕ, Relation.ReflTransGen (AvoidStep x) v (R.up^[j] v)
  | 0 => Relation.ReflTransGen.refl
  | j + 1 => by
    have ih := walk_up hv j
    rw [Function.iterate_succ_apply']
    by_cases hu : IsRoot R (R.up^[j] v)
    · rw [up_eq_self_of_isRoot R hu]; exact ih
    · obtain ⟨g, hg⟩ := exists_high_of_not_isRoot R hu
      refine Relation.ReflTransGen.tail ih ⟨?_, ?_⟩
      · rw [← hg, R.up_high]; exact adj_symm (adj_low_high R g)
      · intro hEq
        have a := R.rank_iterate_up_le j v
        have b := rank_up_lt_of_not_isRoot R hu
        rw [hEq] at b
        omega

/-- Descending to `w` from any of its ancestors avoids every vertex that is not an
ancestor of `w`. -/
theorem walk_down {x w : T.V} (hw : ¬ AncEq R x w) :
    ∀ j : ℕ, Relation.ReflTransGen (AvoidStep x) (R.up^[j] w) w
  | 0 => Relation.ReflTransGen.refl
  | j + 1 => by
    have ih := walk_down hw j
    rw [Function.iterate_succ_apply']
    by_cases hu : IsRoot R (R.up^[j] w)
    · rw [up_eq_self_of_isRoot R hu]; exact ih
    · obtain ⟨g, hg⟩ := exists_high_of_not_isRoot R hu
      refine Relation.ReflTransGen.head ⟨?_, fun hEq ↦ hw ⟨j, hEq⟩⟩ ih
      rw [← hg, R.up_high]; exact adj_low_high R g

/-- **From walk convexity to ancestor convexity.**  If no walk from the parent of
`high e` that avoids `high e` reaches a vertex of `S`, then every vertex of `S` lies
below `high e`. -/
theorem ancEq_of_walk {r : T.V} (hr : ∀ v, AncEq R r v) (e : T.edges) (S : T.V → Prop)
    (hWalk : ∀ w, Relation.ReflTransGen (AvoidStep (R.high e)) (R.low e) w → ¬ S w)
    (w : T.V) (hw : S w) : AncEq R (R.high e) w := by
  by_contra hNot
  obtain ⟨k, hk⟩ := hr (R.low e)
  obtain ⟨j, hj⟩ := hr w
  have h1 := walk_up R (R.rank_low_lt e) k
  have h2 := walk_down R hNot j
  rw [hk] at h1
  rw [hj] at h2
  exact hWalk w (h1.trans h2) hw

end Tree
/-! ## 3. The top of a sheet's anchor region -/

section Label

variable {T : CFGraph.{0}} {d : ℕ} (R : TreeRank T)

/-- `x` is a top of the anchor region of the sheet `σ`: `σ` is in the anchor at `x`
but not in the anchor at the parent of `x`. -/
def Top (A : T.V → Fin d → Prop) (σ : Fin d) (x : T.V) : Prop :=
  A x σ ∧ ∀ e : T.edges, R.high e = x → ¬ A (R.low e) σ

open Classical in
/-- The top of the anchor region of `σ`, when it has one. -/
noncomputable def label (A : T.V → Fin d → Prop) (σ : Fin d) : Option T.V :=
  if h : ∃ x, Top R A σ x then some h.choose else none

/-- **Ancestor convexity** of an anchor predicate: a sheet leaving the anchor on the
way up from `high e` never re-enters it outside the subtree of `high e`. -/
def Convex (A : T.V → Fin d → Prop) : Prop :=
  ∀ (e : T.edges) (σ : Fin d), A (R.high e) σ → ¬ A (R.low e) σ →
    ∀ w, A w σ → AncEq R (R.high e) w

variable {R} {A : T.V → Fin d → Prop} {r : T.V}

theorem top_high_iff (e : T.edges) (σ : Fin d) :
    Top R A σ (R.high e) ↔ A (R.high e) σ ∧ ¬ A (R.low e) σ := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2 e rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun e' he' ↦ ?_⟩
    rw [R.high_injective he']; exact h2

theorem top_root_iff {x : T.V} (hx : IsRoot R x) (σ : Fin d) : Top R A σ x ↔ A x σ :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun e he ↦ absurd he (hx e)⟩⟩

theorem ancEq_of_top (hConv : Convex R A) (hReach : ∀ v, AncEq R r v)
    {σ : Fin d} {x w : T.V} (hx : Top R A σ x) (hw : A w σ) : AncEq R x w := by
  by_cases hRoot : IsRoot R x
  · obtain ⟨k, hk⟩ := hReach x
    rw [iterate_up_of_isRoot R hRoot] at hk
    rw [hk]; exact hReach w
  · obtain ⟨e, rfl⟩ := exists_high_of_not_isRoot R hRoot
    exact hConv e σ hx.1 (hx.2 e rfl) w hw

theorem top_unique (hConv : Convex R A) (hReach : ∀ v, AncEq R r v) {σ : Fin d} {x y : T.V}
    (hx : Top R A σ x) (hy : Top R A σ y) : x = y :=
  ancEq_antisymm R (ancEq_of_top hConv hReach hx hy.1) (ancEq_of_top hConv hReach hy hx.1)

theorem label_eq_some_iff (hConv : Convex R A) (hReach : ∀ v, AncEq R r v) (σ : Fin d)
    (x : T.V) : label R A σ = some x ↔ Top R A σ x := by
  unfold label
  split_ifs with h
  · rw [Option.some_inj]
    exact ⟨fun hEq ↦ hEq ▸ h.choose_spec, fun hx ↦ top_unique hConv hReach h.choose_spec hx⟩
  · simp only [false_iff]
    exact fun hx ↦ h ⟨x, hx⟩

theorem sum_card_fiber (f : Fin d → Option T.V) :
    (univ.filter fun σ ↦ f σ = none).card +
      ∑ x : T.V, (univ.filter fun σ ↦ f σ = some x).card = d := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := (univ : Finset (Fin d)))
    (t := (univ : Finset (Option T.V))) (by intro _ _; simp)
  rw [Finset.card_univ, Fintype.card_fin, Fintype.sum_option] at h
  exact h.symm

open Classical in
theorem card_top (hConv : Convex R A) (hReach : ∀ v, AncEq R r v) (x : T.V) :
    (univ.filter fun σ ↦ label R A σ = some x).card =
      (univ.filter fun σ ↦ Top R A σ x).card := by
  classical
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  exact label_eq_some_iff hConv hReach σ x

variable [∀ v, DecidablePred (A v)] {B : T.V → Fin d → Prop} [∀ v, DecidablePred (B v)]

/-- **Equal anchor counts give equal label fibres.** -/
theorem card_label_eq (hConvA : Convex R A) (hConvB : Convex R B)
    (hReach : ∀ v, AncEq R r v)
    (hV : ∀ v, (univ.filter (A v)).card = (univ.filter (B v)).card)
    (hE : ∀ e : T.edges, (univ.filter fun σ ↦ A (R.high e) σ ∧ A (R.low e) σ).card =
      (univ.filter fun σ ↦ B (R.high e) σ ∧ B (R.low e) σ).card) :
    ∀ c : Option T.V, (univ.filter fun σ ↦ label R A σ = c).card =
      (univ.filter fun σ ↦ label R B σ = c).card := by
  classical
  have hSome : ∀ x : T.V, (univ.filter fun σ ↦ label R A σ = some x).card =
      (univ.filter fun σ ↦ label R B σ = some x).card := by
    intro x
    rw [card_top hConvA hReach, card_top hConvB hReach]
    by_cases hx : IsRoot R x
    · have eA : (univ.filter fun σ ↦ Top R A σ x) = univ.filter (A x) := by
        ext σ; simp only [mem_filter, mem_univ, true_and]; exact top_root_iff hx σ
      have eB : (univ.filter fun σ ↦ Top R B σ x) = univ.filter (B x) := by
        ext σ; simp only [mem_filter, mem_univ, true_and]; exact top_root_iff hx σ
      rw [eA, eB, hV x]
    · obtain ⟨e, rfl⟩ := exists_high_of_not_isRoot R hx
      have eA : (univ.filter fun σ ↦ Top R A σ (R.high e)) =
          univ.filter (fun σ ↦ A (R.high e) σ ∧ ¬ (A (R.high e) σ ∧ A (R.low e) σ)) := by
        ext σ; simp only [mem_filter, mem_univ, true_and]; rw [top_high_iff]; tauto
      have eB : (univ.filter fun σ ↦ Top R B σ (R.high e)) =
          univ.filter (fun σ ↦ B (R.high e) σ ∧ ¬ (B (R.high e) σ ∧ B (R.low e) σ)) := by
        ext σ; simp only [mem_filter, mem_univ, true_and]; rw [top_high_iff]; tauto
      rw [eA, eB]
      have k1 := card_filter_and_not (A (R.high e)) (fun σ ↦ A (R.high e) σ ∧ A (R.low e) σ)
        (fun _ h ↦ h.1)
      have k2 := card_filter_and_not (B (R.high e)) (fun σ ↦ B (R.high e) σ ∧ B (R.low e) σ)
        (fun _ h ↦ h.1)
      have := hV (R.high e)
      have := hE e
      omega
  intro c
  rcases c with _ | x
  · have h1 := sum_card_fiber (label R A)
    have h2 := sum_card_fiber (label R B)
    rw [Finset.sum_congr rfl fun x _ ↦ hSome x] at h1
    omega
  · exact hSome x

end Label
/-! ## 4. The recursive assembly of the vertex permutations -/

section Build

variable {T : CFGraph.{0}} {d : ℕ} (R : TreeRank T)

open Classical in
/-- **The permutations, built from the root down.**  At the root the base is `ρ`; at
`high e` it is the permutation at `low e` corrected by `κ e`.  Every base is then
adjusted by `fix`. -/
noncomputable def buildPerm (ρ : Equiv.Perm (Fin d))
    (κ : T.edges → Equiv.Perm (Fin d) → Equiv.Perm (Fin d))
    (fix : T.V → Equiv.Perm (Fin d) → Equiv.Perm (Fin d)) (v : T.V) : Equiv.Perm (Fin d) :=
  fix v (if h : ∃ e, R.high e = v then
      buildPerm ρ κ fix (R.low h.choose) * κ h.choose (buildPerm ρ κ fix (R.low h.choose))
    else ρ)
termination_by R.rank v
decreasing_by
  have := R.rank_low_lt h.choose
  rw [h.choose_spec] at this
  exact this

variable (ρ : Equiv.Perm (Fin d)) (κ : T.edges → Equiv.Perm (Fin d) → Equiv.Perm (Fin d))
  (fix : T.V → Equiv.Perm (Fin d) → Equiv.Perm (Fin d))

theorem buildPerm_root {v : T.V} (hv : IsRoot R v) :
    buildPerm R ρ κ fix v = fix v ρ := by
  rw [buildPerm, dif_neg (by rintro ⟨e, he⟩; exact hv e he)]

theorem buildPerm_high (e : T.edges) :
    buildPerm R ρ κ fix (R.high e) =
      fix (R.high e) (buildPerm R ρ κ fix (R.low e) * κ e (buildPerm R ρ κ fix (R.low e))) := by
  have key : ∀ h : ∃ e', R.high e' = R.high e, h.choose = e :=
    fun h ↦ R.high_injective h.choose_spec
  rw [buildPerm, dif_pos ⟨e, rfl⟩, key]

end Build
/-! ## 5. The sheet permutations of two star data over one rooted tree -/

section Sheets

variable {T : CFGraph.{0}} {d : ℕ} (R : TreeRank T)
  (P₁ P₂ : T.V → SheetPartition d) (a₁ a₂ : T.V → Fin d)

/-- The anchor predicate: `σ` lies in the block of the anchor sheet `a v`. -/
abbrev Anchor (P : T.V → SheetPartition d) (a : T.V → Fin d) (v : T.V) (σ : Fin d) : Prop :=
  (P v).Rel σ (a v)

/-- The admissible corrections at the parent occurrence `e`: supported on the anchor
at `low e`, carrying the part of it inside the anchor at `high e` onto the sheets that
`p` sends into the second anchor at `high e`. -/
def Good (e : T.edges) (p κ : Equiv.Perm (Fin d)) : Prop :=
  (∀ σ, ¬ Anchor P₁ a₁ (R.low e) σ → κ σ = σ) ∧
    ∀ σ, Anchor P₁ a₁ (R.low e) σ → Anchor P₁ a₁ (R.low e) (κ σ) ∧
      (Anchor P₂ a₂ (R.high e) (p (κ σ)) ↔ Anchor P₁ a₁ (R.high e) σ)

open Classical in
/-- A chosen admissible correction. -/
noncomputable def kappaOf (e : T.edges) (p : Equiv.Perm (Fin d)) : Equiv.Perm (Fin d) :=
  if h : ∃ κ, Good R P₁ P₂ a₁ a₂ e p κ then h.choose else 1

/-- The adjustment sending the first anchor representative at `v` to the second. -/
def fixAt (v : T.V) (p : Equiv.Perm (Fin d)) : Equiv.Perm (Fin d) :=
  p * Equiv.swap ((P₁ v).repr (a₁ v)) (p.symm ((P₂ v).repr (a₂ v)))

open Classical in
/-- A chosen label-preserving permutation. -/
noncomputable def rootPerm : Equiv.Perm (Fin d) :=
  if h : ∃ ρ : Equiv.Perm (Fin d),
      ∀ σ, label R (Anchor P₂ a₂) (ρ σ) = label R (Anchor P₁ a₁) σ
  then h.choose else 1

/-- **The vertex permutations.** -/
noncomputable def vertexPerm : T.V → Equiv.Perm (Fin d) :=
  buildPerm R (rootPerm R P₁ P₂ a₁ a₂) (kappaOf R P₁ P₂ a₁ a₂) (fixAt P₁ P₂ a₁ a₂)

/-- The two invariants carried down the tree: the anchor is matched, and every label
of a vertex that is not an ancestor is preserved. -/
def Inv (v : T.V) (p : Equiv.Perm (Fin d)) : Prop :=
  (∀ σ, Anchor P₂ a₂ v (p σ) ↔ Anchor P₁ a₁ v σ) ∧
    ∀ x, ¬ AncEq R x v → ∀ σ,
      (label R (Anchor P₂ a₂) (p σ) = some x ↔ label R (Anchor P₁ a₁) σ = some x)

variable {R P₁ P₂ a₁ a₂} {r : T.V}

theorem fixAt_repr (v : T.V) (p : Equiv.Perm (Fin d)) :
    fixAt P₁ P₂ a₁ a₂ v p ((P₁ v).repr (a₁ v)) = (P₂ v).repr (a₂ v) := by
  simp [fixAt, Equiv.Perm.mul_apply]

theorem fixAt_inv (hConvA : Convex R (Anchor P₁ a₁)) (hConvB : Convex R (Anchor P₂ a₂))
    (hReach : ∀ v, AncEq R r v) {v : T.V} {p : Equiv.Perm (Fin d)}
    (hp : Inv R P₁ P₂ a₁ a₂ v p) : Inv R P₁ P₂ a₁ a₂ v (fixAt P₁ P₂ a₁ a₂ v p) := by
  have hA1 : Anchor P₁ a₁ v ((P₁ v).repr (a₁ v)) := (P₁ v).rel_repr_left _
  have hA2 : Anchor P₁ a₁ v (p.symm ((P₂ v).repr (a₂ v))) :=
    (hp.1 _).mp (by rw [Equiv.apply_symm_apply]; exact (P₂ v).rel_repr_left _)
  have hq := swap_mem_iff (Anchor P₁ a₁ v) hA1 hA2
  refine ⟨fun σ ↦ ?_, fun x hx σ ↦ ?_⟩
  · simp only [fixAt, Equiv.Perm.mul_apply]
    rw [hp.1, hq]
  · by_cases hσ : Anchor P₁ a₁ v σ
    · have hB : Anchor P₂ a₂ v (fixAt P₁ P₂ a₁ a₂ v p σ) := by
        simp only [fixAt, Equiv.Perm.mul_apply]
        rw [hp.1, hq]; exact hσ
      constructor
      · intro h
        rw [label_eq_some_iff hConvB hReach] at h
        exact absurd (ancEq_of_top hConvB hReach h hB) hx
      · intro h
        rw [label_eq_some_iff hConvA hReach] at h
        exact absurd (ancEq_of_top hConvA hReach h hσ) hx
    · simp only [fixAt, Equiv.Perm.mul_apply]
      rw [swap_apply_of_not _ hA1 hA2 hσ]
      exact hp.2 x hx σ

theorem kappaOf_spec (e : T.edges) {p : Equiv.Perm (Fin d)}
    (h : ∃ κ, Good R P₁ P₂ a₁ a₂ e p κ) : Good R P₁ P₂ a₁ a₂ e p (kappaOf R P₁ P₂ a₁ a₂ e p) := by
  unfold kappaOf
  rw [dif_pos h]
  exact h.choose_spec

theorem inv_base_high (hConvA : Convex R (Anchor P₁ a₁)) (hConvB : Convex R (Anchor P₂ a₂))
    (hReach : ∀ v, AncEq R r v) (e : T.edges) {p κ : Equiv.Perm (Fin d)}
    (hp : Inv R P₁ P₂ a₁ a₂ (R.low e) p) (hκ : Good R P₁ P₂ a₁ a₂ e p κ) :
    Inv R P₁ P₂ a₁ a₂ (R.high e) (p * κ) := by
  refine ⟨fun σ ↦ ?_, fun x hx σ ↦ ?_⟩
  · rw [Equiv.Perm.mul_apply]
    by_cases hu : Anchor P₁ a₁ (R.low e) σ
    · exact (hκ.2 σ hu).2
    · rw [hκ.1 σ hu]
      have h1 : Anchor P₁ a₁ (R.high e) σ ↔ label R (Anchor P₁ a₁) σ = some (R.high e) := by
        rw [label_eq_some_iff hConvA hReach, top_high_iff]; tauto
      have hpu := hp.1 σ
      have h2 : Anchor P₂ a₂ (R.high e) (p σ) ↔
          label R (Anchor P₂ a₂) (p σ) = some (R.high e) := by
        rw [label_eq_some_iff hConvB hReach, top_high_iff]; tauto
      rw [h1, h2]
      exact hp.2 _ (not_ancEq_high_low R e) σ
  · have hxu : ¬ AncEq R x (R.low e) := fun h ↦ hx (ancEq_high_of_ancEq_low R e h)
    rw [Equiv.Perm.mul_apply]
    by_cases hu : Anchor P₁ a₁ (R.low e) σ
    · have hB : Anchor P₂ a₂ (R.low e) (p (κ σ)) := (hp.1 _).mpr (hκ.2 σ hu).1
      constructor
      · intro h
        rw [label_eq_some_iff hConvB hReach] at h
        exact absurd (ancEq_of_top hConvB hReach h hB) hxu
      · intro h
        rw [label_eq_some_iff hConvA hReach] at h
        exact absurd (ancEq_of_top hConvA hReach h hu) hxu
    · rw [hκ.1 σ hu]
      exact hp.2 x hxu σ

variable [∀ v, DecidablePred (Anchor P₁ a₁ v)] [∀ v, DecidablePred (Anchor P₂ a₂ v)]

theorem rootPerm_spec (hConvA : Convex R (Anchor P₁ a₁)) (hConvB : Convex R (Anchor P₂ a₂))
    (hReach : ∀ v, AncEq R r v)
    (hV : ∀ v, (univ.filter (Anchor P₁ a₁ v)).card = (univ.filter (Anchor P₂ a₂ v)).card)
    (hE : ∀ e : T.edges,
      (univ.filter fun σ ↦ Anchor P₁ a₁ (R.high e) σ ∧ Anchor P₁ a₁ (R.low e) σ).card =
      (univ.filter fun σ ↦ Anchor P₂ a₂ (R.high e) σ ∧ Anchor P₂ a₂ (R.low e) σ).card)
    (σ : Fin d) :
    label R (Anchor P₂ a₂) (rootPerm R P₁ P₂ a₁ a₂ σ) = label R (Anchor P₁ a₁) σ := by
  classical
  have hex : ∃ ρ : Equiv.Perm (Fin d),
      ∀ σ, label R (Anchor P₂ a₂) (ρ σ) = label R (Anchor P₁ a₁) σ :=
    exists_perm_of_card_fiber _ _ (card_label_eq hConvA hConvB hReach hV hE)
  unfold rootPerm
  rw [dif_pos hex]
  exact hex.choose_spec σ

theorem inv_root (hConvA : Convex R (Anchor P₁ a₁)) (hConvB : Convex R (Anchor P₂ a₂))
    (hReach : ∀ v, AncEq R r v)
    (hV : ∀ v, (univ.filter (Anchor P₁ a₁ v)).card = (univ.filter (Anchor P₂ a₂ v)).card)
    (hE : ∀ e : T.edges,
      (univ.filter fun σ ↦ Anchor P₁ a₁ (R.high e) σ ∧ Anchor P₁ a₁ (R.low e) σ).card =
      (univ.filter fun σ ↦ Anchor P₂ a₂ (R.high e) σ ∧ Anchor P₂ a₂ (R.low e) σ).card)
    {v : T.V} (hv : IsRoot R v) : Inv R P₁ P₂ a₁ a₂ v (rootPerm R P₁ P₂ a₁ a₂) := by
  have hSpec := rootPerm_spec hConvA hConvB hReach hV hE
  refine ⟨fun σ ↦ ?_, fun x _ σ ↦ by rw [hSpec]⟩
  have h1 := label_eq_some_iff hConvB hReach (rootPerm R P₁ P₂ a₁ a₂ σ) v
  have h2 := label_eq_some_iff hConvA hReach σ v
  rw [hSpec] at h1
  exact (top_root_iff (A := Anchor P₂ a₂) hv _).symm.trans
    (h1.symm.trans (h2.trans (top_root_iff hv _)))

theorem good_exists
    (hE : ∀ e : T.edges,
      (univ.filter fun σ ↦ Anchor P₁ a₁ (R.high e) σ ∧ Anchor P₁ a₁ (R.low e) σ).card =
      (univ.filter fun σ ↦ Anchor P₂ a₂ (R.high e) σ ∧ Anchor P₂ a₂ (R.low e) σ).card)
    (e : T.edges) {p : Equiv.Perm (Fin d)}
    (hp : ∀ σ, Anchor P₂ a₂ (R.low e) (p σ) ↔ Anchor P₁ a₁ (R.low e) σ) :
    ∃ κ, Good R P₁ P₂ a₁ a₂ e p κ := by
  classical
  have hCard : (univ.filter fun σ ↦ Anchor P₁ a₁ (R.low e) σ ∧ Anchor P₁ a₁ (R.high e) σ).card =
      (univ.filter fun σ ↦ Anchor P₁ a₁ (R.low e) σ ∧ Anchor P₂ a₂ (R.high e) (p σ)).card := by
    have h1 : (univ.filter fun σ ↦ Anchor P₁ a₁ (R.low e) σ ∧ Anchor P₁ a₁ (R.high e) σ) =
        univ.filter fun σ ↦ Anchor P₁ a₁ (R.high e) σ ∧ Anchor P₁ a₁ (R.low e) σ := by
      ext σ; simp only [mem_filter, mem_univ, true_and]; exact and_comm
    have h2 : (univ.filter fun σ ↦ Anchor P₁ a₁ (R.low e) σ ∧ Anchor P₂ a₂ (R.high e) (p σ)) =
        univ.filter fun σ ↦ (fun τ ↦ Anchor P₂ a₂ (R.high e) τ ∧ Anchor P₂ a₂ (R.low e) τ)
          (p σ) := by
      ext σ; simp only [mem_filter, mem_univ, true_and]; rw [hp]; exact and_comm
    rw [h1, h2]
    exact (hE e).trans (card_filter_comp_perm p
      (fun τ ↦ Anchor P₂ a₂ (R.high e) τ ∧ Anchor P₂ a₂ (R.low e) τ)).symm
  obtain ⟨κ, hκ1, hκ2⟩ := exists_perm_on (Anchor P₁ a₁ (R.low e))
    (fun σ ↦ Anchor P₁ a₁ (R.low e) σ ∧ Anchor P₁ a₁ (R.high e) σ)
    (fun σ ↦ Anchor P₁ a₁ (R.low e) σ ∧ Anchor P₂ a₂ (R.high e) (p σ))
    (fun _ h ↦ h.1) (fun _ h ↦ h.1) hCard
  refine ⟨κ, hκ1, fun σ hσ ↦ ⟨(hκ2 σ hσ).1, ?_⟩⟩
  have := (hκ2 σ hσ).2
  simp only [(hκ2 σ hσ).1, hσ, true_and] at this
  exact this

/-- **The invariants hold at every vertex.** -/
theorem inv_vertexPerm (hConvA : Convex R (Anchor P₁ a₁)) (hConvB : Convex R (Anchor P₂ a₂))
    (hReach : ∀ v, AncEq R r v)
    (hV : ∀ v, (univ.filter (Anchor P₁ a₁ v)).card = (univ.filter (Anchor P₂ a₂ v)).card)
    (hE : ∀ e : T.edges,
      (univ.filter fun σ ↦ Anchor P₁ a₁ (R.high e) σ ∧ Anchor P₁ a₁ (R.low e) σ).card =
      (univ.filter fun σ ↦ Anchor P₂ a₂ (R.high e) σ ∧ Anchor P₂ a₂ (R.low e) σ).card) :
    ∀ n (v : T.V), R.rank v = n → Inv R P₁ P₂ a₁ a₂ v (vertexPerm R P₁ P₂ a₁ a₂ v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    by_cases hRoot : IsRoot R v
    · show Inv R P₁ P₂ a₁ a₂ v (buildPerm R _ _ _ v)
      rw [buildPerm_root R _ _ _ hRoot]
      exact fixAt_inv hConvA hConvB hReach (inv_root hConvA hConvB hReach hV hE hRoot)
    · obtain ⟨e, rfl⟩ := exists_high_of_not_isRoot R hRoot
      have hLow : Inv R P₁ P₂ a₁ a₂ (R.low e) (vertexPerm R P₁ P₂ a₁ a₂ (R.low e)) :=
        ih _ (by rw [← hv]; exact R.rank_low_lt e) _ rfl
      show Inv R P₁ P₂ a₁ a₂ (R.high e) (buildPerm R _ _ _ (R.high e))
      rw [buildPerm_high R _ _ _ e]
      exact fixAt_inv hConvA hConvB hReach (inv_base_high hConvA hConvB hReach e hLow
        (kappaOf_spec e (good_exists hE e hLow.1)))

end Sheets
/-! ## 6. The occurrence permutations, and the abstract matching theorem -/

section Edges

variable {T : CFGraph.{0}} {d : ℕ} (R : TreeRank T)
  (P₁ P₂ : T.V → SheetPartition d) (a₁ a₂ : T.V → Fin d)
  (Q₁ Q₂ : T.edges → SheetPartition d) (kind : T.edges → Prop)

/-- The sheets in the anchors at both ends of `e`. -/
abbrev Both (P : T.V → SheetPartition d) (a : T.V → Fin d) (e : T.edges) (σ : Fin d) : Prop :=
  Anchor P a (R.low e) σ ∧ Anchor P a (R.high e) σ

/-- The base permutation over `e`: the vertex permutation at `low e`, corrected. -/
noncomputable def edgeBase (e : T.edges) : Equiv.Perm (Fin d) :=
  vertexPerm R P₁ P₂ a₁ a₂ (R.low e) *
    kappaOf R P₁ P₂ a₁ a₂ e (vertexPerm R P₁ P₂ a₁ a₂ (R.low e))

open Classical in
/-- The adjustment sending the first occurrence-anchor representative to the second. -/
noncomputable def edgeFix (e : T.edges) : Equiv.Perm (Fin d) :=
  if h : kind e ∧ ∃ σ, Both R P₁ a₁ e σ then
    Equiv.swap ((Q₁ e).repr h.2.choose)
      ((edgeBase R P₁ P₂ a₁ a₂ e).symm ((Q₂ e).repr (edgeBase R P₁ P₂ a₁ a₂ e h.2.choose)))
  else 1

/-- **The occurrence permutations.** -/
noncomputable def edgePerm (e : T.edges) : Equiv.Perm (Fin d) :=
  edgeBase R P₁ P₂ a₁ a₂ e * edgeFix R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e

theorem eq_relabel_of_repr (P Q : SheetPartition d) (π : Equiv.Perm (Fin d))
    (h : ∀ σ, Q.repr (π σ) = π (P.repr σ)) : Q = P.relabel π := by
  apply SheetPartition.ext_repr
  funext i
  show Q.repr i = π (P.repr (π.symm i))
  rw [← h, Equiv.apply_symm_apply]

variable {R P₁ P₂ a₁ a₂ Q₁ Q₂ kind} {r : T.V}
  [∀ v, DecidablePred (Anchor P₁ a₁ v)] [∀ v, DecidablePred (Anchor P₂ a₂ v)]

/-- **The abstract matching theorem.**  Two star data over one rooted tree -- every
vertex partition one anchor block and singletons, every occurrence partition either
discrete or the common part of its two end anchors plus singletons, the same kind on
both sides -- whose anchors are ancestor-convex and have the same sizes at every vertex
and over every occurrence, are related by vertex and occurrence permutations
compatible along every occurrence. -/
theorem exists_sheetPerms (hReach : ∀ v, AncEq R r v)
    (hConvA : Convex R (Anchor P₁ a₁)) (hConvB : Convex R (Anchor P₂ a₂))
    (hStarA : ∀ v σ, ¬ Anchor P₁ a₁ v σ → (P₁ v).repr σ = σ)
    (hStarB : ∀ v σ, ¬ Anchor P₂ a₂ v σ → (P₂ v).repr σ = σ)
    (hEdgeA : ∀ e σ τ, (Q₁ e).Rel σ τ ↔
      σ = τ ∨ (kind e ∧ Both R P₁ a₁ e σ ∧ Both R P₁ a₁ e τ))
    (hEdgeB : ∀ e σ τ, (Q₂ e).Rel σ τ ↔
      σ = τ ∨ (kind e ∧ Both R P₂ a₂ e σ ∧ Both R P₂ a₂ e τ))
    (hV : ∀ v, (univ.filter (Anchor P₁ a₁ v)).card = (univ.filter (Anchor P₂ a₂ v)).card)
    (hE : ∀ e : T.edges,
      (univ.filter fun σ ↦ Anchor P₁ a₁ (R.high e) σ ∧ Anchor P₁ a₁ (R.low e) σ).card =
      (univ.filter fun σ ↦ Anchor P₂ a₂ (R.high e) σ ∧ Anchor P₂ a₂ (R.low e) σ).card) :
    (∀ v, P₂ v = (P₁ v).relabel (vertexPerm R P₁ P₂ a₁ a₂ v)) ∧
      (∀ e, Q₂ e = (Q₁ e).relabel (edgePerm R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e)) ∧
      ∀ (e : T.edges) (v : T.V),
        ((e : T.V × T.V).1 = v ∨ (e : T.V × T.V).2 = v) → ∀ σ,
          (P₁ v).Rel ((vertexPerm R P₁ P₂ a₁ a₂ v).symm
            (edgePerm R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ)) σ := by
  classical
  have hInv : ∀ v, Inv R P₁ P₂ a₁ a₂ v (vertexPerm R P₁ P₂ a₁ a₂ v) :=
    fun v ↦ inv_vertexPerm hConvA hConvB hReach hV hE _ v rfl
  -- the representative of the anchor goes to the representative
  have hRepr : ∀ v, vertexPerm R P₁ P₂ a₁ a₂ v ((P₁ v).repr (a₁ v)) = (P₂ v).repr (a₂ v) := by
    intro v
    by_cases hRoot : IsRoot R v
    · show buildPerm R _ _ _ v _ = _
      rw [buildPerm_root R _ _ _ hRoot]; exact fixAt_repr v _
    · obtain ⟨e, rfl⟩ := exists_high_of_not_isRoot R hRoot
      show buildPerm R _ _ _ (R.high e) _ = _
      rw [buildPerm_high R _ _ _ e]; exact fixAt_repr _ _
  -- the correction at every occurrence
  have hGood : ∀ e : T.edges, Good R P₁ P₂ a₁ a₂ e (vertexPerm R P₁ P₂ a₁ a₂ (R.low e))
      (kappaOf R P₁ P₂ a₁ a₂ e (vertexPerm R P₁ P₂ a₁ a₂ (R.low e))) :=
    fun e ↦ kappaOf_spec e (good_exists hE e (hInv (R.low e)).1)
  have hBaseInv : ∀ e : T.edges, Inv R P₁ P₂ a₁ a₂ (R.high e) (edgeBase R P₁ P₂ a₁ a₂ e) :=
    fun e ↦ inv_base_high hConvA hConvB hReach e (hInv (R.low e)) (hGood e)
  have hVHigh : ∀ e : T.edges, vertexPerm R P₁ P₂ a₁ a₂ (R.high e) =
      fixAt P₁ P₂ a₁ a₂ (R.high e) (edgeBase R P₁ P₂ a₁ a₂ e) :=
    fun e ↦ buildPerm_high R _ _ _ e
  have hBaseLow : ∀ (e : T.edges) τ, Anchor P₂ a₂ (R.low e) (edgeBase R P₁ P₂ a₁ a₂ e τ) ↔
      Anchor P₁ a₁ (R.low e) τ := by
    intro e τ
    simp only [edgeBase, Equiv.Perm.mul_apply]
    rw [(hInv (R.low e)).1]
    by_cases hτ : Anchor P₁ a₁ (R.low e) τ
    · exact iff_of_true ((hGood e).2 τ hτ).1 hτ
    · rw [(hGood e).1 τ hτ]
  have hBaseBoth : ∀ (e : T.edges) τ, Both R P₂ a₂ e (edgeBase R P₁ P₂ a₁ a₂ e τ) ↔
      Both R P₁ a₁ e τ := fun e τ ↦ and_congr (hBaseLow e τ) ((hBaseInv e).1 τ)
  -- the occurrence adjustment is supported on `Both`
  have hFix : ∀ (e : T.edges) (S : Fin d → Prop), (∀ σ, Both R P₁ a₁ e σ → S σ) →
      (∀ σ, S (edgeFix R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ) ↔ S σ) ∧
        ∀ σ, ¬ S σ → edgeFix R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ = σ := by
    intro e S hS
    unfold edgeFix
    split_ifs with h
    · have hs₁ : Both R P₁ a₁ e ((Q₁ e).repr h.2.choose) := by
        rcases (hEdgeA e _ _).mp ((Q₁ e).rel_repr_left h.2.choose) with h' | h'
        · rw [h']; exact h.2.choose_spec
        · exact h'.2.1
      have hx : Both R P₂ a₂ e (edgeBase R P₁ P₂ a₁ a₂ e h.2.choose) :=
        (hBaseBoth e _).mpr h.2.choose_spec
      have hs₂ : Both R P₂ a₂ e ((Q₂ e).repr (edgeBase R P₁ P₂ a₁ a₂ e h.2.choose)) := by
        rcases (hEdgeB e _ _).mp ((Q₂ e).rel_repr_left
            (edgeBase R P₁ P₂ a₁ a₂ e h.2.choose)) with h' | h'
        · rw [h']; exact hx
        · exact h'.2.1
      have ht : Both R P₁ a₁ e ((edgeBase R P₁ P₂ a₁ a₂ e).symm
          ((Q₂ e).repr (edgeBase R P₁ P₂ a₁ a₂ e h.2.choose))) :=
        (hBaseBoth e _).mp (by rw [Equiv.apply_symm_apply]; exact hs₂)
      exact ⟨swap_mem_iff S (hS _ hs₁) (hS _ ht),
        fun σ hσ ↦ swap_apply_of_not S (hS _ hs₁) (hS _ ht) hσ⟩
    · exact ⟨fun σ ↦ by rw [Equiv.Perm.one_apply], fun σ _ ↦ Equiv.Perm.one_apply σ⟩
  refine ⟨fun v ↦ ?_, fun e ↦ ?_, fun e v hv σ ↦ ?_⟩
  · -- vertex partitions
    apply eq_relabel_of_repr
    intro σ
    by_cases hσ : Anchor P₁ a₁ v σ
    · have h1 : (P₁ v).repr σ = (P₁ v).repr (a₁ v) := hσ
      have h2 : (P₂ v).repr (vertexPerm R P₁ P₂ a₁ a₂ v σ) = (P₂ v).repr (a₂ v) :=
        ((hInv v).1 σ).mpr hσ
      rw [h1, h2, hRepr]
    · rw [hStarA v σ hσ, hStarB v _ (fun h ↦ hσ (((hInv v).1 σ).mp h))]
  · -- occurrence partitions
    apply eq_relabel_of_repr
    intro σ
    have hPermBoth : ∀ τ, Both R P₂ a₂ e (edgePerm R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e τ) ↔
        Both R P₁ a₁ e τ := by
      intro τ
      simp only [edgePerm, Equiv.Perm.mul_apply]
      rw [hBaseBoth]
      exact (hFix e (Both R P₁ a₁ e) (fun _ h ↦ h)).1 τ
    by_cases hc : kind e ∧ Both R P₁ a₁ e σ
    · have h : kind e ∧ ∃ σ, Both R P₁ a₁ e σ := ⟨hc.1, σ, hc.2⟩
      have hμ : edgeFix R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e = Equiv.swap ((Q₁ e).repr h.2.choose)
          ((edgeBase R P₁ P₂ a₁ a₂ e).symm
            ((Q₂ e).repr (edgeBase R P₁ P₂ a₁ a₂ e h.2.choose))) := by
        unfold edgeFix; rw [dif_pos h]
      have h1 : (Q₁ e).repr σ = (Q₁ e).repr h.2.choose :=
        (hEdgeA e σ h.2.choose).mpr (Or.inr ⟨hc.1, hc.2, h.2.choose_spec⟩)
      have hx : Both R P₂ a₂ e (edgeBase R P₁ P₂ a₁ a₂ e h.2.choose) :=
        (hBaseBoth e _).mpr h.2.choose_spec
      have h2 : (Q₂ e).repr (edgePerm R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ) =
          (Q₂ e).repr (edgeBase R P₁ P₂ a₁ a₂ e h.2.choose) :=
        (hEdgeB e _ _).mpr (Or.inr ⟨hc.1, (hPermBoth σ).mpr hc.2, hx⟩)
      rw [h1, h2]
      simp only [edgePerm, Equiv.Perm.mul_apply, hμ, Equiv.swap_apply_left,
        Equiv.apply_symm_apply]
    · have h1 : (Q₁ e).repr σ = σ := by
        rcases (hEdgeA e _ _).mp ((Q₁ e).rel_repr_left σ) with h' | h'
        · exact h'
        · exact absurd ⟨h'.1, h'.2.2⟩ hc
      have h2 : (Q₂ e).repr (edgePerm R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ) =
          edgePerm R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ := by
        rcases (hEdgeB e _ _).mp ((Q₂ e).rel_repr_left
            (edgePerm R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ)) with h' | h'
        · exact h'
        · exact absurd ⟨h'.1, (hPermBoth σ).mp h'.2.2⟩ hc
      rw [h1, h2]
  · -- compatibility
    have hRel : ∀ (w : T.V) (x : Fin d), Anchor P₁ a₁ w x → Anchor P₁ a₁ w σ →
        (P₁ w).Rel x σ := fun w x hx hσ ↦ hx.trans hσ.symm
    rcases R.eq_low_or_eq_high hv with rfl | rfl
    · have hμ := hFix e (Anchor P₁ a₁ (R.low e)) (fun _ h ↦ h.1)
      have hEq : (vertexPerm R P₁ P₂ a₁ a₂ (R.low e)).symm
          (edgePerm R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ) =
          kappaOf R P₁ P₂ a₁ a₂ e (vertexPerm R P₁ P₂ a₁ a₂ (R.low e))
            (edgeFix R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ) := by
        simp only [edgePerm, edgeBase, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
      rw [hEq]
      by_cases hσ : Anchor P₁ a₁ (R.low e) σ
      · exact hRel _ _ ((hGood e).2 _ ((hμ.1 σ).mpr hσ)).1 hσ
      · rw [hμ.2 σ hσ, (hGood e).1 σ hσ]
        exact rfl
    · have hμ := hFix e (Anchor P₁ a₁ (R.high e)) (fun _ h ↦ h.2)
      set base := edgeBase R P₁ P₂ a₁ a₂ e with hbase
      have hA1 : Anchor P₁ a₁ (R.high e) ((P₁ (R.high e)).repr (a₁ (R.high e))) :=
        (P₁ (R.high e)).rel_repr_left _
      have hA2 : Anchor P₁ a₁ (R.high e) (base.symm ((P₂ (R.high e)).repr (a₂ (R.high e)))) :=
        ((hBaseInv e).1 _).mp (by
          rw [Equiv.apply_symm_apply]
          exact (P₂ (R.high e)).rel_repr_left _)
      set q := Equiv.swap ((P₁ (R.high e)).repr (a₁ (R.high e)))
        (base.symm ((P₂ (R.high e)).repr (a₂ (R.high e)))) with hq
      have hEq : (vertexPerm R P₁ P₂ a₁ a₂ (R.high e)).symm
          (edgePerm R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ) =
          q (edgeFix R P₁ P₂ a₁ a₂ Q₁ Q₂ kind e σ) := by
        rw [Equiv.symm_apply_eq, hVHigh e]
        simp only [fixAt, edgePerm, Equiv.Perm.mul_apply, ← hbase, ← hq]
        rw [hq, Equiv.swap_apply_self]
      rw [hEq]
      by_cases hσ : Anchor P₁ a₁ (R.high e) σ
      · exact hRel _ _ ((swap_mem_iff _ hA1 hA2 _).mpr ((hμ.1 σ).mpr hσ)) hσ
      · rw [hμ.2 σ hσ, swap_apply_of_not _ hA1 hA2 hσ]
        exact rfl

end Edges

/-! ## 7. Every diagonal member is a convex star datum -/

section Member

open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.DanglingSideStructure
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.Count.FibreCaterpillar (catCore)
open DraismaVargas.Count.DiagonalTargetIso

variable {m : ℕ} {y : Fin (6 * m + 3) → ℚ} (member : FibreMember (catCore m) y (m + 2))

/-- A source vertex meeting a surviving occurrence survives. -/
theorem nonDanglingValency_pos_of_incident {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) {edge : data.SourceEdge} {X : data.SourceVertex}
    (hSurv : ¬ IsDangling data edge) (hInc : Incident data edge X) :
    0 < nonDanglingValency data X := by
  by_contra h
  exact hSurv (((nonDanglingValency_eq_zero_iff data X).mp (by omega)) edge hInc)

/-- Every target vertex carries a surviving source vertex. -/
theorem exists_anchor (v : member.target.V) :
    ∃ X : member.data.SourceVertex, X.1.1 = v ∧ 0 < nonDanglingValency member.data X := by
  have := member.fullDim.nontrivial_target
  obtain ⟨g, hg⟩ := SegmentWalls.exists_incident_occurrence member.fullDim.targetConnected v
  obtain ⟨E, hE, hSurv⟩ := member.fullDim.noDanglingTargetFibres g
  refine ⟨member.data.sourceEndpoint v E.1.2, rfl, ?_⟩
  refine nonDanglingValency_pos_of_incident member.data hSurv ?_
  rcases hg with h | h
  · left
    show member.data.sourceEndpoint (E.1.1 : member.target.V × member.target.V).1 E.1.2 = _
    rw [hE, h]
  · right
    show member.data.sourceEndpoint (E.1.1 : member.target.V × member.target.V).2 E.1.2 = _
    rw [hE, h]

/-- **The anchor**: the surviving source vertex over `v` (unique, by
`TrivalentFibreUnique`). -/
noncomputable def anchorVertex (v : member.target.V) : member.data.SourceVertex :=
  (exists_anchor member v).choose

theorem anchorVertex_target (v : member.target.V) : (anchorVertex member v).1.1 = v :=
  (exists_anchor member v).choose_spec.1

theorem anchorVertex_pos (v : member.target.V) :
    0 < nonDanglingValency member.data (anchorVertex member v) :=
  (exists_anchor member v).choose_spec.2

/-- The sheet naming the anchor. -/
noncomputable def anchorSheet (v : member.target.V) : Fin (m + 2) := (anchorVertex member v).1.2

/-- The anchor predicate of a member. -/
abbrev MAnchor (v : member.target.V) (σ : Fin (m + 2)) : Prop :=
  (member.data.vertexPartition v).Rel σ (anchorSheet member v)

theorem eq_anchorVertex {X : member.data.SourceVertex} {v : member.target.V} (hX : X.1.1 = v)
    (hPos : 0 < nonDanglingValency member.data X) : X = anchorVertex member v :=
  TrivalentFibreUnique.fibreVertexUnique member X _ (hX.trans (anchorVertex_target member v).symm)
    hPos (anchorVertex_pos member v)

theorem sourceEndpoint_eq_anchor_iff (v : member.target.V) (σ : Fin (m + 2)) :
    member.data.sourceEndpoint v σ = anchorVertex member v ↔ MAnchor member v σ := by
  rw [GluingDatum.sourceEndpoint_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have h := anchorVertex_target member v
    unfold MAnchor anchorSheet
    convert h2 using 2
  · intro h
    refine ⟨(anchorVertex_target member v).symm, ?_⟩
    have hv := anchorVertex_target member v
    unfold MAnchor anchorSheet at h
    convert h using 2

theorem nonDanglingValency_eq_zero_of_not_anchor {v : member.target.V} {σ : Fin (m + 2)}
    (hσ : ¬ MAnchor member v σ) :
    nonDanglingValency member.data (member.data.sourceEndpoint v σ) = 0 := by
  by_contra h
  exact hσ ((sourceEndpoint_eq_anchor_iff member v σ).mp
    (eq_anchorVertex member rfl (Nat.pos_of_ne_zero h)))

/-- **Vertex partitions are stars around the anchor.** -/
theorem repr_eq_self_of_not_anchor {v : member.target.V} {σ : Fin (m + 2)}
    (hσ : ¬ MAnchor member v σ) : (member.data.vertexPartition v).repr σ = σ := by
  have h := PartitionCensusProof.vertex_blockCard_eq_one_off_surviving member
    (anchorVertex member v) (anchorVertex_pos member v) σ
  rw [anchorVertex_target member v] at h
  exact repr_eq_self_of_blockCard_eq_one _ (h hσ)

/-- An occurrence over `g` through `σ` has its two ends over the two ends of `g`. -/
theorem sourceEnds_sourceEdge' (g : member.target.edges) (σ : Fin (m + 2)) :
    member.data.sourceEnds (member.data.sourceEdge g σ) =
      (member.data.sourceEndpoint (g : member.target.V × member.target.V).1 σ,
        member.data.sourceEndpoint (g : member.target.V × member.target.V).2 σ) :=
  CaterpillarDatum.sourceEnds_sourceEdge member.data g σ

/-- The sheets of a surviving occurrence lie in the anchors at both ends. -/
theorem anchor_of_survives {g : member.target.edges} {σ : Fin (m + 2)}
    (hSurv : ¬ IsDangling member.data (member.data.sourceEdge g σ)) :
    MAnchor member (g : member.target.V × member.target.V).1 σ ∧
      MAnchor member (g : member.target.V × member.target.V).2 σ := by
  have hEnds := sourceEnds_sourceEdge' member g σ
  constructor
  · refine (sourceEndpoint_eq_anchor_iff member _ σ).mp (eq_anchorVertex member rfl ?_)
    exact nonDanglingValency_pos_of_incident member.data hSurv (Or.inl (by rw [hEnds]))
  · refine (sourceEndpoint_eq_anchor_iff member _ σ).mp (eq_anchorVertex member rfl ?_)
    exact nonDanglingValency_pos_of_incident member.data hSurv (Or.inr (by rw [hEnds]))

/-- The kind of an occurrence: it is not the edge of a loop slot. -/
def MKind (g : member.target.edges) : Prop := ¬ IsLeafEdge m ((slotEdge member).symm g)

/-- **Occurrence partitions**: over the edge of a non-leaf slot, one block made of the
sheets in both end anchors, and singletons; over a loop slot's edge, discrete. -/
theorem edge_rel_iff (hD : member.Diagonal) (g : member.target.edges) (σ τ : Fin (m + 2)) :
    (member.data.edgePartition g).Rel σ τ ↔ σ = τ ∨
      (MKind member g ∧
        (MAnchor member (g : member.target.V × member.target.V).1 σ ∧
          MAnchor member (g : member.target.V × member.target.V).2 σ) ∧
        (MAnchor member (g : member.target.V × member.target.V).1 τ ∧
          MAnchor member (g : member.target.V × member.target.V).2 τ)) := by
  classical
  set t := (slotEdge member).symm g with ht
  have hg : slotEdge member t = g := by rw [ht, Equiv.apply_symm_apply]
  constructor
  · intro h
    by_cases hστ : σ = τ
    · exact Or.inl hστ
    right
    have hCard : 1 < (member.data.edgePartition g).blockCard σ := by
      have hsub : ({σ, τ} : Finset (Fin (m + 2))) ⊆ (member.data.edgePartition g).block σ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (member.data.edgePartition g).self_mem_block _
        · exact ((member.data.edgePartition g).mem_block_iff _ _).mpr h
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hστ] at this
      exact this
    have hSurv : ¬ IsDangling member.data (member.data.sourceEdge g σ) := by
      intro hd
      have h1 := member.fullDim.danglingEdgeNoGlue _ hd
      rw [GluingDatum.sourceEdgeIndex_sourceEdge] at h1
      omega
    have hτ : member.data.sourceEdge g τ = member.data.sourceEdge g σ :=
      Subtype.ext (Prod.ext rfl h.symm)
    refine ⟨?_, anchor_of_survives member hSurv, anchor_of_survives member (by rw [hτ]; exact hSurv)⟩
    intro hLeaf
    have hLoop : (catCore m).tail t = (catCore m).head t :=
      (LollipopLeafRow.catCore_tail_eq_head_iff m t).mpr hLeaf
    have h1 := PartitionCensusProof.edge_blockCard_leaf member hD ⟨t, hLoop⟩ σ
    simp only [hg] at h1
    omega
  · rintro (rfl | ⟨hk, hσ, hτ⟩)
    · rfl
    obtain ⟨E, -, hR⟩ := BallotResidues.exists_incident_of_coreIncidence_pos member
      ((catCore m).tail t) t (coreIncidence_tail_pos t)
    have hT : E.1.1.1 = g := by rw [target_eq_slotEdge member hD E, hR, hg]
    have e1 : ((member.data.sourceEnds E.1).1).1.1 = (g : member.target.V × member.target.V).1 := by
      show (E.1.1.1 : member.target.V × member.target.V).1 = _
      rw [hT]
    have e2 : ((member.data.sourceEnds E.1).2).1.1 = (g : member.target.V × member.target.V).2 := by
      show (E.1.1.1 : member.target.V × member.target.V).2 = _
      rw [hT]
    have hEEnds : member.data.sourceEnds E.1 =
        (anchorVertex member (g : member.target.V × member.target.V).1,
          anchorVertex member (g : member.target.V × member.target.V).2) :=
      Prod.ext (eq_anchorVertex member e1 (nonDanglingValency_pos_of_incident member.data E.2 (Or.inl rfl)))
        (eq_anchorVertex member e2 (nonDanglingValency_pos_of_incident member.data E.2 (Or.inr rfl)))
    have key : ∀ ρ, MAnchor member (g : member.target.V × member.target.V).1 ρ ∧
        MAnchor member (g : member.target.V × member.target.V).2 ρ →
          member.data.sourceEdge g ρ = E.1 := by
      intro ρ hρ
      by_cases hF : IsDangling member.data (member.data.sourceEdge g ρ)
      · by_contra hne
        refine CaterpillarPruning.not_isDangling_of_parallel member.data hne ?_ hF
        rw [hEEnds, sourceEnds_sourceEdge', (sourceEndpoint_eq_anchor_iff member _ ρ).mpr hρ.1,
          (sourceEndpoint_eq_anchor_iff member _ ρ).mpr hρ.2]
      · have hRow := PartitionCensusProof.row_eq_of_target_eq member hD
          ⟨member.data.sourceEdge g ρ, hF⟩ (t := t) (by show g = _; rw [hg])
        have := eq_of_row_eq_of_not_leaf member hD hk hRow hR
        exact congrArg Subtype.val this
    have h1 := key σ hσ
    have h2 := key τ hτ
    have h3 := congrArg (fun F : member.data.SourceEdge ↦ F.1.2) (h1.trans h2.symm)
    exact h3

/-- A target walk avoiding `x` lifts, sheet by sheet, to a source walk avoiding the
vertex of that sheet over `x`. -/
theorem reachP_of_walk {x z w : member.target.V} (σ : Fin (m + 2))
    (hWalk : Relation.ReflTransGen (AvoidStep x) z w) :
    ReachP member.data.sourceGraph (fun X ↦ X ≠ member.data.sourceEndpoint x σ)
      (member.data.sourceEndpoint z σ) (member.data.sourceEndpoint w σ) := by
  induction hWalk with
  | refl => exact reachP_refl _ _
  | tail _ hStep ih =>
    rename_i u u' _
    obtain ⟨⟨g, hg⟩, hne⟩ := hStep
    refine reachP_tail ih ?_ ?_
    · apply num_edges_pos_of_sourceEnds member.data (edge := member.data.sourceEdge g σ)
      rw [sourceEnds_sourceEdge']
      rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [h1, h2]
      · right; rw [h1, h2]
    · intro hEq
      exact hne (congrArg (fun X : member.data.SourceVertex ↦ X.1.1) hEq)

/-- **Walk convexity of the anchors of a member.**  If the sheet `σ` is in the anchor
at `x` but not at its neighbour `z`, then no walk from `z` that avoids `x` reaches an
anchor containing `σ`: the occurrence of `σ` over `xz` is dangling (its end over `z`
does not survive), its genus-zero side is the one containing `z`, and that side
contains every vertex such a walk reaches -- none of which survives. -/
theorem convex_walk (g : member.target.edges) {x z : member.target.V}
    (hxz : ((g : member.target.V × member.target.V).1 = x ∧
        (g : member.target.V × member.target.V).2 = z) ∨
      ((g : member.target.V × member.target.V).1 = z ∧
        (g : member.target.V × member.target.V).2 = x))
    {σ : Fin (m + 2)} (hx : MAnchor member x σ) (hz : ¬ MAnchor member z σ) (w : member.target.V)
    (hWalk : Relation.ReflTransGen (AvoidStep x) z w) : ¬ MAnchor member w σ := by
  intro hw
  have hEnds := sourceEnds_sourceEdge' member g σ
  have hXpos : 0 < nonDanglingValency member.data (member.data.sourceEndpoint x σ) := by
    rw [(sourceEndpoint_eq_anchor_iff member x σ).mpr hx]; exact anchorVertex_pos member x
  have hWpos : 0 < nonDanglingValency member.data (member.data.sourceEndpoint w σ) := by
    rw [(sourceEndpoint_eq_anchor_iff member w σ).mpr hw]; exact anchorVertex_pos member w
  have hZ0 := nonDanglingValency_eq_zero_of_not_anchor member hz
  have hReach := reachP_of_walk member σ hWalk
  have hIncZ : Incident member.data (member.data.sourceEdge g σ)
      (member.data.sourceEndpoint z σ) := by
    rcases hxz with ⟨_, h2⟩ | ⟨h1, _⟩
    · right; rw [hEnds, h2]
    · left; rw [hEnds, h1]
  have hDang := ((nonDanglingValency_eq_zero_iff member.data _).mp hZ0) _ hIncZ
  -- the side containing the anchor end cannot be the genus-zero side
  have hInner : ∀ {inner outer : member.data.SourceVertex},
      DanglingSide member.data.sourceGraph inner outer →
        inner = member.data.sourceEndpoint x σ → False := by
    intro inner outer cut h
    have := nonDanglingValency_eq_zero_of_mem_side member.data cut cut.left_mem
    rw [h] at this
    omega
  have hOuter : ∀ {inner outer : member.data.SourceVertex},
      DanglingSide member.data.sourceGraph inner outer →
        inner = member.data.sourceEndpoint z σ → outer = member.data.sourceEndpoint x σ →
          False := by
    intro inner outer cut h1 h2
    subst h1 h2
    have := nonDanglingValency_eq_zero_of_mem_side member.data cut
      (mem_side_of_reachP cut cut.left_mem hReach)
    omega
  unfold IsDangling at hDang
  rw [hEnds] at hDang
  rcases hDang with h | h <;> obtain ⟨cut⟩ := h <;> rcases hxz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hInner cut (by rw [h1])
  · exact hOuter cut (by rw [h1]) (by rw [h2])
  · exact hOuter cut (by rw [h2]) (by rw [h1])
  · exact hInner cut (by rw [h2])

/-- **Over a loop slot's edge the two end anchors share exactly two sheets**: those of
the tip's anchor (`LeafFibre.coreVertex`, of size two), both of whose
occurrences survive. -/
theorem card_both_of_not_kind (hD : member.Diagonal) (g : member.target.edges)
    (hKind : ¬ MKind member g) :
    (univ.filter fun σ ↦ MAnchor member (g : member.target.V × member.target.V).1 σ ∧
      MAnchor member (g : member.target.V × member.target.V).2 σ).card = 2 := by
  classical
  set t := (slotEdge member).symm g with ht
  have hg : slotEdge member t = g := by rw [ht, Equiv.apply_symm_apply]
  have hL : IsLeafEdge m t := not_not.mp hKind
  have hLoop : (catCore m).tail t = (catCore m).head t :=
    (LollipopLeafRow.catCore_tail_eq_head_iff m t).mpr hL
  set z := absMap member (Sum.inr ⟨t, hLoop⟩) with hz
  have hLv : IsLeafVertex member.target z := PartitionCensusProof.isLeafVertex_tip member hD ⟨t, hLoop⟩
  have hAbs : absEnds m t = (Sum.inl ((catCore m).tail t), Sum.inr ⟨t, hLoop⟩) := by
    unfold absEnds; rw [dif_pos hLoop]
  have hZ : (g : member.target.V × member.target.V).1 = z ∨
      (g : member.target.V × member.target.V).2 = z := by
    rcases slotEdge_absEnds member hD t with h | h <;> rw [hg, hAbs] at h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hCore : anchorVertex member z = LeafFibre.coreVertex member.fullDim hLv :=
    (eq_anchorVertex member (LeafFibre.coreVertex_target member.fullDim hLv)
      (by rw [LeafFibre.nonDanglingValency_coreVertex]; norm_num)).symm
  have hBoth : ∀ σ, MAnchor member z σ →
      MAnchor member (g : member.target.V × member.target.V).1 σ ∧
        MAnchor member (g : member.target.V × member.target.V).2 σ := by
    intro σ hσ
    apply anchor_of_survives member
    apply LeafFibre.not_isDangling_of_incident_coreVertex member.fullDim hLv
    rw [← hCore, ← (sourceEndpoint_eq_anchor_iff member z σ).mpr hσ]
    rcases hZ with h | h
    · left; rw [sourceEnds_sourceEdge', h]
    · right; rw [sourceEnds_sourceEdge', h]
  have hEq : (univ.filter fun σ ↦ MAnchor member (g : member.target.V × member.target.V).1 σ ∧
      MAnchor member (g : member.target.V × member.target.V).2 σ) =
      (member.data.vertexPartition z).block (anchorSheet member z) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, SheetPartition.mem_block_iff]
    constructor
    · intro h
      rcases hZ with h' | h'
      · rw [← h']; exact h.1.symm
      · rw [← h']; exact h.2.symm
    · intro h
      exact hBoth σ h.symm
  rw [hEq]
  have h2 := LeafFibre.blockCard_coreBlock member.fullDim hLv
  have h3 : anchorSheet member z = (LeafFibre.coreBlock member.fullDim hLv).1 := by
    unfold anchorSheet; rw [hCore]; rfl
  rw [h3]
  exact h2

end Member

/-! ## 8. The census gives the anchor sizes -/

section Census

variable {d : ℕ}

/-- A partition all of whose blocks but the one of `a` are singletons, in iff form. -/
theorem star_rel_iff (P : SheetPartition d) (a : Fin d)
    (h : ∀ σ, ¬ P.Rel σ a → P.repr σ = σ) (σ τ : Fin d) :
    P.Rel σ τ ↔ σ = τ ∨ (P.Rel σ a ∧ P.Rel τ a) := by
  constructor
  · intro hστ
    by_cases hσ : P.Rel σ a
    · exact Or.inr ⟨hσ, hστ.symm.trans hσ⟩
    · by_cases hτ : P.Rel τ a
      · exact absurd (hστ.trans hτ) hσ
      · left
        have e1 := h σ hσ
        have e2 := h τ hτ
        have : P.repr σ = P.repr τ := hστ
        rw [e1, e2] at this
        exact this
  · rintro (rfl | ⟨h1, h2⟩)
    · rfl
    · exact h1.trans h2.symm

theorem card_le_of_relabel (P Q : SheetPartition d) (S S' : Fin d → Prop) [DecidablePred S]
    [DecidablePred S'] (hP : ∀ σ τ, P.Rel σ τ ↔ σ = τ ∨ (S σ ∧ S τ))
    (hQ : ∀ σ τ, Q.Rel σ τ ↔ σ = τ ∨ (S' σ ∧ S' τ)) (π : Equiv.Perm (Fin d))
    (hπ : Q = P.relabel π) (h2 : 1 < (univ.filter S).card) :
    (univ.filter S).card ≤ (univ.filter S').card := by
  refine Finset.card_le_card_of_injOn π ?_ (fun a _ b _ h ↦ π.injective h)
  intro ρ hρ
  have hρ' : S ρ := (mem_filter.mp hρ).2
  obtain ⟨ρ', hρ'mem, hne⟩ := Finset.exists_mem_ne h2 ρ
  have hRel : P.Rel ρ' ρ := (hP ρ' ρ).mpr (Or.inr ⟨(mem_filter.mp hρ'mem).2, hρ'⟩)
  have hRelQ : Q.Rel (π ρ') (π ρ) := by
    rw [hπ]; exact (SheetPartition.relabel_rel_iff P π ρ' ρ).mpr hRel
  rcases (hQ _ _).mp hRelQ with h | h
  · exact absurd (π.injective h) hne
  · exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, h.2⟩)

/-- **Two stars related by a relabelling have anchors of the same size.** -/
theorem star_card_eq (P Q : SheetPartition d) (S S' : Fin d → Prop) [DecidablePred S]
    [DecidablePred S'] (hP : ∀ σ τ, P.Rel σ τ ↔ σ = τ ∨ (S σ ∧ S τ))
    (hQ : ∀ σ τ, Q.Rel σ τ ↔ σ = τ ∨ (S' σ ∧ S' τ)) (π : Equiv.Perm (Fin d))
    (hπ : Q = P.relabel π) (hS : ∃ σ, S σ) (hS' : ∃ σ, S' σ) :
    (univ.filter S).card = (univ.filter S').card := by
  have hπ' : P = Q.relabel π.symm := by
    rw [hπ, SheetPartition.relabel_relabel]
    apply SheetPartition.ext_repr
    funext i
    simp [SheetPartition.relabel]
  have p1 : 0 < (univ.filter S).card := by
    obtain ⟨σ, hσ⟩ := hS; exact Finset.card_pos.mpr ⟨σ, by simpa using hσ⟩
  have p2 : 0 < (univ.filter S').card := by
    obtain ⟨σ, hσ⟩ := hS'; exact Finset.card_pos.mpr ⟨σ, by simpa using hσ⟩
  by_cases h : 1 < (univ.filter S).card
  · have a := card_le_of_relabel P Q S S' hP hQ π hπ h
    have b := card_le_of_relabel Q P S' S hQ hP π.symm hπ' (by omega)
    omega
  · by_cases h' : 1 < (univ.filter S').card
    · have b := card_le_of_relabel Q P S' S hQ hP π.symm hπ' h'
      omega
    · omega

end Census

/-! ## 9. The global matching -/

section Assembly

open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.Count.FibreCaterpillar (catCore)
open DraismaVargas.Count.DiagonalTargetIso

variable {T₁ T₂ : CFGraph.{0}}

/-- A walk avoiding `x` is carried by a target layer to a walk avoiding the image of `x`. -/
theorem walk_map (L : TargetLayer T₁ T₂) {x z w : T₁.V}
    (h : Relation.ReflTransGen (AvoidStep x) z w) :
    Relation.ReflTransGen (AvoidStep (L.targetVertex x)) (L.targetVertex z)
      (L.targetVertex w) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hStep ih =>
    obtain ⟨⟨g, hg⟩, hne⟩ := hStep
    refine Relation.ReflTransGen.tail ih ⟨⟨L.targetEdge g, ?_⟩,
      fun hEq ↦ hne (L.targetVertex.injective hEq)⟩
    rcases L.ends g with h | h <;> rw [h] <;> rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [h1, h2, and_self, true_or, or_true]

theorem and_ends_iff (R : TreeRank T₁) (e : T₁.edges) (S : T₁.V → Prop) :
    (S (e : T₁.V × T₁.V).1 ∧ S (e : T₁.V × T₁.V).2) ↔ (S (R.low e) ∧ S (R.high e)) := by
  rcases R.ends e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  exact and_comm

theorem and_layer_ends_iff (L : TargetLayer T₁ T₂) (e : T₁.edges) (S : T₂.V → Prop) :
    (S (L.targetEdge e : T₂.V × T₂.V).1 ∧ S (L.targetEdge e : T₂.V × T₂.V).2) ↔
      (S (L.targetVertex (e : T₁.V × T₁.V).1) ∧ S (L.targetVertex (e : T₁.V × T₁.V).2)) := by
  rcases L.ends e with h | h <;> rw [h]
  exact and_comm

variable {m : ℕ} {y₁ y₂ : Fin (6 * m + 3) → ℚ}

theorem mKind_layer_iff (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2)) (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal)
    (e : mem₁.target.edges) :
    MKind mem₂ ((targetLayer mem₁ mem₂ hD₁ hD₂).targetEdge e) ↔ MKind mem₁ e := by
  obtain ⟨t, rfl⟩ := (slotEdge mem₁).surjective e
  unfold MKind
  rw [targetLayer_slotEdge, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Every occurrence of a member carries a sheet in both end anchors. -/
theorem exists_both (member : FibreMember (catCore m) y₁ (m + 2)) (g : member.target.edges) :
    ∃ σ, MAnchor member (g : member.target.V × member.target.V).1 σ ∧
      MAnchor member (g : member.target.V × member.target.V).2 σ := by
  obtain ⟨E, hE, hSurv⟩ := member.fullDim.noDanglingTargetFibres g
  refine ⟨E.1.2, anchor_of_survives member ?_⟩
  have : member.data.sourceEdge g E.1.2 = E := by
    rw [← hE]; exact GluingDatum.sourceEdge_self member.data E
  rw [this]; exact hSurv

/-- **The global matching.**  Two diagonal members whose partitions are, over Half 1's
target layer, relabellings of each other at every vertex and every occurrence have a
sheet layer over that target layer. -/
theorem sheetLayer_of_census (mem₁ : FibreMember (catCore m) y₁ (m + 2))
    (mem₂ : FibreMember (catCore m) y₂ (m + 2)) (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal)
    (hCensus : (∀ v, ∃ π : Equiv.Perm (Fin (m + 2)),
        mem₂.data.vertexPartition ((targetLayer mem₁ mem₂ hD₁ hD₂).targetVertex v) =
          (mem₁.data.vertexPartition v).relabel π) ∧
      (∀ e, ∃ π : Equiv.Perm (Fin (m + 2)),
        mem₂.data.edgePartition ((targetLayer mem₁ mem₂ hD₁ hD₂).targetEdge e) =
          (mem₁.data.edgePartition e).relabel π)) :
    Nonempty (SheetLayer mem₁.data mem₂.data (targetLayer mem₁ mem₂ hD₁ hD₂)) := by
  classical
  set L := targetLayer mem₁ mem₂ hD₁ hD₂ with hL
  obtain ⟨R⟩ := exists_treeRank mem₁.target mem₁.fullDim.targetConnected
    mem₁.fullDim.targetGenus
  obtain ⟨r, -, hReach⟩ := exists_root R mem₁.fullDim.targetConnected
  let P₁ : mem₁.target.V → SheetPartition (m + 2) := fun v ↦ mem₁.data.vertexPartition v
  let P₂ : mem₁.target.V → SheetPartition (m + 2) :=
    fun v ↦ mem₂.data.vertexPartition (L.targetVertex v)
  let a₁ : mem₁.target.V → Fin (m + 2) := fun v ↦ anchorSheet mem₁ v
  let a₂ : mem₁.target.V → Fin (m + 2) := fun v ↦ anchorSheet mem₂ (L.targetVertex v)
  let Q₁ : mem₁.target.edges → SheetPartition (m + 2) := fun e ↦ mem₁.data.edgePartition e
  let Q₂ : mem₁.target.edges → SheetPartition (m + 2) :=
    fun e ↦ mem₂.data.edgePartition (L.targetEdge e)
  have hConvA : Convex R (Anchor P₁ a₁) := by
    intro e σ h1 h2 w hw
    refine ancEq_of_walk R hReach e (fun w ↦ Anchor P₁ a₁ w σ) (fun w hWalk ↦ ?_) w hw
    refine convex_walk mem₁ e ?_ h1 h2 w hWalk
    rcases R.ends e with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inr ⟨e1, e2⟩
    · exact Or.inl ⟨e1, e2⟩
  have hConvB : Convex R (Anchor P₂ a₂) := by
    intro e σ h1 h2 w hw
    refine ancEq_of_walk R hReach e (fun w ↦ Anchor P₂ a₂ w σ) (fun w hWalk ↦ ?_) w hw
    refine convex_walk mem₂ (L.targetEdge e) ?_ h1 h2 (L.targetVertex w) (walk_map L hWalk)
    rcases R.ends e with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases L.ends e with h | h <;> rw [h, e1, e2]
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hStarA : ∀ v σ, ¬ Anchor P₁ a₁ v σ → (P₁ v).repr σ = σ :=
    fun v σ h ↦ repr_eq_self_of_not_anchor mem₁ h
  have hStarB : ∀ v σ, ¬ Anchor P₂ a₂ v σ → (P₂ v).repr σ = σ :=
    fun v σ h ↦ repr_eq_self_of_not_anchor mem₂ h
  have hEdgeA : ∀ e σ τ, (Q₁ e).Rel σ τ ↔
      σ = τ ∨ (MKind mem₁ e ∧ Both R P₁ a₁ e σ ∧ Both R P₁ a₁ e τ) := by
    intro e σ τ
    rw [edge_rel_iff mem₁ hD₁ e σ τ, and_ends_iff R e (fun v ↦ MAnchor mem₁ v σ),
      and_ends_iff R e (fun v ↦ MAnchor mem₁ v τ)]
  have hEdgeB : ∀ e σ τ, (Q₂ e).Rel σ τ ↔
      σ = τ ∨ (MKind mem₁ e ∧ Both R P₂ a₂ e σ ∧ Both R P₂ a₂ e τ) := by
    intro e σ τ
    rw [edge_rel_iff mem₂ hD₂ (L.targetEdge e) σ τ, mKind_layer_iff mem₁ mem₂ hD₁ hD₂ e,
      and_layer_ends_iff L e (fun v ↦ MAnchor mem₂ v σ),
      and_layer_ends_iff L e (fun v ↦ MAnchor mem₂ v τ),
      and_ends_iff R e (fun v ↦ MAnchor mem₂ (L.targetVertex v) σ),
      and_ends_iff R e (fun v ↦ MAnchor mem₂ (L.targetVertex v) τ)]
  have hV : ∀ v, (univ.filter (Anchor P₁ a₁ v)).card = (univ.filter (Anchor P₂ a₂ v)).card := by
    intro v
    obtain ⟨π, hπ⟩ := hCensus.1 v
    exact star_card_eq (P₁ v) (P₂ v) _ _
      (star_rel_iff (P₁ v) (a₁ v) (hStarA v)) (star_rel_iff (P₂ v) (a₂ v) (hStarB v)) π hπ
      ⟨a₁ v, rfl⟩ ⟨a₂ v, rfl⟩
  have hE : ∀ e : mem₁.target.edges,
      (univ.filter fun σ ↦ Anchor P₁ a₁ (R.high e) σ ∧ Anchor P₁ a₁ (R.low e) σ).card =
      (univ.filter fun σ ↦ Anchor P₂ a₂ (R.high e) σ ∧ Anchor P₂ a₂ (R.low e) σ).card := by
    intro e
    have eA : (univ.filter fun σ ↦ Anchor P₁ a₁ (R.high e) σ ∧ Anchor P₁ a₁ (R.low e) σ) =
        univ.filter fun σ ↦ MAnchor mem₁ (e : mem₁.target.V × mem₁.target.V).1 σ ∧
          MAnchor mem₁ (e : mem₁.target.V × mem₁.target.V).2 σ := by
      ext σ
      simp only [mem_filter, mem_univ, true_and]
      rw [and_ends_iff R e (fun v ↦ MAnchor mem₁ v σ)]
      exact and_comm
    have eB : (univ.filter fun σ ↦ Anchor P₂ a₂ (R.high e) σ ∧ Anchor P₂ a₂ (R.low e) σ) =
        univ.filter fun σ ↦
          MAnchor mem₂ (L.targetEdge e : mem₂.target.V × mem₂.target.V).1 σ ∧
          MAnchor mem₂ (L.targetEdge e : mem₂.target.V × mem₂.target.V).2 σ := by
      ext σ
      simp only [mem_filter, mem_univ, true_and]
      rw [and_layer_ends_iff L e (fun v ↦ MAnchor mem₂ v σ),
        and_ends_iff R e (fun v ↦ MAnchor mem₂ (L.targetVertex v) σ)]
      exact and_comm
    rw [eA, eB]
    by_cases hk : MKind mem₁ e
    · obtain ⟨π, hπ⟩ := hCensus.2 e
      refine star_card_eq (Q₁ e) (Q₂ e) _ _ (fun σ τ ↦ ?_) (fun σ τ ↦ ?_) π hπ
        (exists_both mem₁ e) (exists_both mem₂ (L.targetEdge e))
      · rw [edge_rel_iff mem₁ hD₁ e σ τ]
        simp only [hk, true_and]
      · rw [edge_rel_iff mem₂ hD₂ (L.targetEdge e) σ τ, mKind_layer_iff mem₁ mem₂ hD₁ hD₂ e]
        simp only [hk, true_and]
    · rw [card_both_of_not_kind mem₁ hD₁ e hk, card_both_of_not_kind mem₂ hD₂ (L.targetEdge e)
        (by rw [mKind_layer_iff mem₁ mem₂ hD₁ hD₂ e]; exact hk)]
  obtain ⟨hVP, hEP, hCompat⟩ := exists_sheetPerms (Q₁ := Q₁) (Q₂ := Q₂) (kind := MKind mem₁)
    hReach hConvA hConvB hStarA hStarB hEdgeA hEdgeB hV hE
  exact ⟨⟨vertexPerm R P₁ P₂ a₁ a₂, edgePerm R P₁ P₂ a₁ a₂ Q₁ Q₂ (MKind mem₁), hVP, hEP,
    hCompat⟩⟩

end Assembly

/-! ## 10. The headlines -/

section Headline

open DraismaVargas.Count.FibreCaterpillar (catCore)
open DraismaVargas.Count.DiagonalTargetIso
open BallotCoreIdentification (ballotFamilyMember)

/-- **The census gives the sheet layer**, at every `m`. -/
theorem sheetLayerSupply_of_partitionCensus {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (h : SheetLayerCensus.PartitionCensus m request) : SheetLayerSupply m request :=
  fun s mem hOpen hOdd hD hDiag ↦
    sheetLayer_of_census _ mem _ hD (h s mem hOpen hOdd hD hDiag)

/-- With the census `PartitionCensusProof.partitionCensus`, **`SheetLayerSupply`
holds outright**, at every `m` and every request. -/
theorem sheetLayerSupply (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    SheetLayerSupply m request :=
  sheetLayerSupply_of_partitionCensus (PartitionCensusProof.partitionCensus m request)

/-- **Any two diagonal members with the same core diagonal have a sheet layer over
Half 1's target layer** (no request, openness, oddness or slope hypothesis). -/
theorem sheetLayer_of_coreDiag_eq {m : ℕ} {y₁ y₂ : Fin (6 * m + 3) → ℚ}
    (mem₁ : FibreMember (catCore m) y₁ (m + 2)) (mem₂ : FibreMember (catCore m) y₂ (m + 2))
    (hD₁ : mem₁.Diagonal) (hD₂ : mem₂.Diagonal) (hDiag : mem₁.coreDiag = mem₂.coreDiag) :
    Nonempty (SheetLayer mem₁.data mem₂.data (targetLayer mem₁ mem₂ hD₁ hD₂)) :=
  sheetLayer_of_census mem₁ mem₂ hD₁ hD₂
    (PartitionCensusProof.partitionCensus_of_coreDiag_eq mem₁ mem₂ hD₁ hD₂ hDiag)

/-- **`hSupply` from the census**, in the binder shape of the `hSupply` hypothesis of
`BallotSpineReversalSheetIso.diagonalClassification_genusSix_of_three_residues`. -/
theorem hSupply_of_partitionCensus
    (h : ∀ request : Fin (6 * 2 + 3) → ℚ,
      SimpleWallSupply.PositiveGeneral (catCore 2) (2 + 2) request →
        SheetLayerCensus.PartitionCensus 2 request) :
    ∀ request : Fin (6 * 2 + 3) → ℚ,
      SimpleWallSupply.PositiveGeneral (catCore 2) (2 + 2) request →
      ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
        mem.Open → mem.HasOddMult → mem.Diagonal →
          mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
            Nonempty (GeometricDatumIso (ballotFamilyMember 2 request s).data mem.data) :=
  fun request hRequest ↦ hSupply_of_sheetLayerSupply
    (sheetLayerSupply_of_partitionCensus (h request hRequest))

/-- **`hSupply`, discharged** (the census and this file's matching). -/
theorem hSupply_genusSix :
    ∀ request : Fin (6 * 2 + 3) → ℚ,
      SimpleWallSupply.PositiveGeneral (catCore 2) (2 + 2) request →
      ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
        mem.Open → mem.HasOddMult → mem.Diagonal →
          mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
            Nonempty (GeometricDatumIso (ballotFamilyMember 2 request s).data mem.data) :=
  hSupply_of_partitionCensus fun request _ ↦ PartitionCensusProof.partitionCensus 2 request

end Headline

/-! ## 11. Inference (i) tested: the root permutation is not free -/

section RootChoice

open DraismaVargas.Count.DiagonalTargetIso
open TargetNormalForm (inPath inPathFirst)

/-- The identity target layer of a graph. -/
def idLayer (T : CFGraph) : TargetLayer T T :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ ↦ UnorderedEnds.refl _⟩

/-- Blocks `{0, 1}` and `{2}`. -/
def partTwo : SheetPartition 3 where
  repr := fun sheet ↦ if sheet = 2 then 2 else 0
  repr_idem := by decide

/-- Discrete at the middle vertex, `{0,1} {2}` at the leaf `0`, `{1} {0,2}` at the leaf
`2`, discrete on both occurrences: a star datum whose sheets `1` and `2` have their
anchor regions in different branches at the middle. -/
def rootDatum : GluingDatum inPath 3 where
  degree_pos := by decide
  vertexPartition v :=
    if v = midV then SheetPartition.discrete 3
    else if v = leftV then partTwo else partOne
  edgePartition _ := SheetPartition.discrete 3
  refines_left _ := SheetPartition.discrete_refines _
  refines_right _ := SheetPartition.discrete_refines _

theorem rootDatum_valid : rootDatum.Valid :=
  ⟨(GluingDatum.checkConnected_eq_true_iff rootDatum).mp (by decide +kernel),
    (GluingDatum.checkRiemannHurwitz_eq_true_iff rootDatum).mp (by decide +kernel)⟩

/-- **The root permutation is not free.**  At the
middle vertex the swap of sheets `1` and `2` realises the census (the partition there
is discrete), yet no sheet layer of `rootDatum` with itself, over the identity, has it
as its middle permutation: compatibility at the discrete middle forces the occurrence
permutation of `inPathFirst` to be that swap, and then compatibility at the leaf `0`
would carry sheet `1` of the block `{0,1}` onto sheet `2`, outside it. -/
theorem root_choice_not_free :
    rootDatum.vertexPartition midV =
        (rootDatum.vertexPartition midV).relabel (Equiv.swap 1 2) ∧
      ∀ L : SheetLayer rootDatum rootDatum (idLayer inPath),
        L.vertexPerm midV ≠ Equiv.swap 1 2 := by
  refine ⟨?_, fun L hL ↦ ?_⟩
  · show SheetPartition.discrete 3 = (SheetPartition.discrete 3).relabel _
    exact (SheetPartition.discrete_relabel _).symm
  have hMid : ∀ σ, L.edgePerm inPathFirst σ = Equiv.swap 1 2 σ := by
    intro σ
    have h := L.compatible inPathFirst midV (Or.inr rfl) σ
    rw [hL] at h
    have h' : (Equiv.swap 1 2).symm (L.edgePerm inPathFirst σ) = σ := h
    rw [Equiv.symm_apply_eq] at h'
    exact h'
  have hLeft : ∀ σ, partTwo.Rel ((L.vertexPerm leftV).symm (L.edgePerm inPathFirst σ)) σ :=
    fun σ ↦ L.compatible inPathFirst leftV (Or.inl rfl) σ
  have hPart : ∀ i j, partTwo.Rel (L.vertexPerm leftV i) (L.vertexPerm leftV j) ↔
      partTwo.Rel i j := by
    intro i j
    have h := L.vertexPartition leftV
    have h' : partTwo = partTwo.relabel (L.vertexPerm leftV) := h
    have h'' := SheetPartition.relabel_rel_iff partTwo (L.vertexPerm leftV) i j
    rw [← h'] at h''
    exact h''
  have key : ∀ (π : Equiv.Perm (Fin 3)), (∀ σ, partTwo.Rel (π.symm (Equiv.swap 1 2 σ)) σ) →
      (∀ i j, partTwo.Rel (π i) (π j) ↔ partTwo.Rel i j) → False := by
    decide
  exact key (L.vertexPerm leftV) (fun σ ↦ by rw [← hMid]; exact hLeft σ) hPart

/-- The data themselves are isomorphic (by the identity), so what fails is the choice
at the root, not the conclusion. -/
theorem rootDatum_self : Nonempty (SheetLayer rootDatum rootDatum (idLayer inPath)) :=
  ⟨SheetLayer.ofId _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)⟩

end RootChoice

end DraismaVargas.Count.SheetLayerMatching
