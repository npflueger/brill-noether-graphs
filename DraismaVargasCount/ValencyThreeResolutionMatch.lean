module

public import DraismaVargasCount.ValencyThreeRigidity
public import DraismaVargasCount.W3ShiftStarExhaustionProof

@[expose] public section

set_option autoImplicit false

/-!
# Valency-three resolution match

A. Vargas, *Catalan-many tropical morphisms to trees; Part II: A space and a count*,
arXiv:2609.09109, subsection "Valency-3 limits: Case {v3-nd4}" (`subsec-case-v3`), with Cases
(r0)/(r1) of `prop-local`.  The valency-three case of the type-change step is organised in
stages by `ValencyThreeSplit` (the two pictures `TwoPicture`/`ThreePicture`, the local
equations, `Reads`) and `ValencyThreeRigidity` (the residual `ResolutionMatch`, and
`splitRigidity_of_resolutionMatch`).  This module proves the resolution match (stage 4) in
general, using the pendant automorphisms of `W3Nd2StarExhaustionProof` (§9--§11).

## The result, in one paragraph

`ValencyThreeRigidity.ResolutionMatch core y degree` holds **at every core, request and
degree, with no hypothesis** (`resolutionMatch`).  Classify the incoming resolution of a cover
on every merged class (§2--§3, the forest count per merged class, `forest_count`, does the
work): off the ramified divalent class every divalent class is unramified, hence one class of
each occurrence there (`block_eq_of_unram`), so the contracted occurrence agrees with the
divalent side and the trivalent side is the whole merged class (`pv_eq_merged`).  On the anchor
the split decides: in the two-vertex picture (`two_shape`) the divalent side is the moving
direction's partition with the classes of `e₂`, `e₅` merged, the contracted occurrence equal to
it, the trivalent side the merged partition; in the three-vertex picture (`three_shape`) the
divalent side is `e_α`'s partition, the trivalent side splits off `A' = ` the class of `e_δ`
(`card_image_eq_succ`: the anchor's divalent class carries two contracted classes, so the
trivalent side has two), and the contracted occurrence is their common refinement, with
`A' ⊆ A_u` and `A'` dangling above the third direction.  Read in limit coordinates
(`cover_two`, `cover_three`, at the placement `placement_facts` isolating the divalent side's
direction), both shapes are determined by the labelled limit, so a labelled isomorphism of
limits transports them (`transportFree_two`, `transportFree_three`) -- after, for base tree
`T_α`, re-choosing the isomorphism by a pendant automorphism on the third direction's branch
that moves the image of `A'` onto `A'` (`exists_realign_set`).

## Main results

* §1 `card_image_fibre`, `fibre_card_one`, `card_image_eq_of_agree`, `card_image_eq_succ`,
  `rel_or_rel_of_card_two`, `exists_perm_image`.
* §2 `rel_of_incident`, `rel_iff_of_index`, `not_rel_of_ne`, `rel_iff_of_two`,
  `block_eq_of_unram`, `ram_zero_of_not_rel`, `forest_count`.
* §3 `refines_merged_u/v`, `contracted_refines_u/v`, `pv_eq_merged`, `block_eq_off`,
  `rel_iff_of_block_eq`, **`two_shape`**, `sourceVertex_eq_of_rel`, **`three_shape`**.
* §4 `MergeRel`, `mergeRel_map`, `ends_of_mem`, `mem_of_ends`, **`transportFree_two`**,
  `anchor_iff`, **`transportFree_three`**.
* §5 `pendant_at_wall_forest` (the pendant hypothesis from the contraction forest alone, no
  nondegenerate request), **`exists_realign_set`**.
* §6 `unfold_mem_ends`, `label_edgePartition`, `label_sheet`, `label_unfold`, `label_mem`,
  **`placement_facts`**.  §7 **`cover_two`**, **`cover_three`**.
* §8 **`resolutionMatch`**.  §9 **`anchorExtension`** (stage 4), **`splitRigidity`** (stages
  4--5 at every facet request over a connected core with `3 ≤ n`), and
  **`facetParity_of_typeMatch`** (`ValencyThreeRigidity.facetParity_of_typeMatch_resolutionMatch`
  with both `ResolutionMatch` inputs discharged).

`resolutionMatch` and `splitRigidity` are used in `ValencyThreeCoreSlots` and
`ValencyTwoResolutionMatch`, on the way to the valency-three and valency-two cases of the
type-change step (step 3 of `DraismaVargasCount.Assembly`).

## Hypotheses

* `resolutionMatch` and `anchorExtension` have no hypothesis beyond their binders; the two
  oddness hypotheses of `ResolutionMatch` are **not used** (the match holds for any two
  regrowths at valency-three anchors reading the same split).
* `splitRigidity` keeps the stage-5 inputs `core.Connected`, `3 ≤ n`, `y e₀ = 0`.
* `facetParity_of_typeMatch` keeps stage 3 on both sides (`TypeMatch`, see
  `ValencyThreeTypeMatch`) and uniqueness at the non-valency-three limits (`hrest`, `hrest'`).

## Remarks

* On the anchor, the incoming resolution has the following shapes.  Two-vertex picture: the
  divalent side is the union of the sheets of `e₂` and `e₅` plus singletons (the `t_u`
  partition off `e₂ ∪ e₅`: the dangling classes, by no-glue), the trivalent side is `{A}`, and
  the contracted occurrence also equals the divalent side.  Three-vertex picture: the divalent
  side is the `t_u` partition, the trivalent side is `{sheets of e_δ, rest}`, and the contracted
  occurrence is their common refinement (not the divalent side).  Off the anchor, the divalent
  side and the new edge are the `t_u` partition and the trivalent side is the join component.
* Coherence through pendant automorphisms is needed only once: in the three-vertex picture,
  for the third direction against `A'` (`transportFree_three`'s `hX`).  The two-vertex picture
  needs no coherence, and neither do the non-anchor classes.  The regrown occurrence
  additionally needs a permutation **inside** `A_u` moving the image of `A'` onto `A'`; that is
  not a limit automorphism (the sheets are not dangling there), and it is absorbed by the free
  `newPerm` of the decoupled transport `ResolutionExpansionFree.TransportFree`.
-/

namespace DraismaVargas.Count.ValencyThreeResolutionMatch

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification W4StableSource
open FullDimensionalSource

/-! ## 1.  Counting blocks, and moving one finite set onto another -/

section Counting

variable {d : ℕ}

/-- **Fibrewise block count.**  The fine blocks inside a closed set, counted over the coarse
blocks they lie in. -/
theorem card_image_fibre (F U : SheetPartition d) (S : Finset (Fin d)) (hFU : F.Refines U)
    (c : Fin d → ℕ)
    (hc : ∀ x ∈ S, ((S.filter (U.Rel x)).image F.repr).card = c (U.repr x)) :
    (S.image F.repr).card = ∑ b ∈ S.image U.repr, c b := by
  classical
  have hUF : ∀ z, U.repr (F.repr z) = U.repr z := fun z ↦ hFU.rel (F.rel_repr_left z)
  rw [Finset.card_eq_sum_card_fiberwise (f := U.repr) (t := S.image U.repr) (fun y hy ↦ by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨x, hx, (hUF x).symm⟩)]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  rw [← hc x hx]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hzx⟩
    exact ⟨z, ⟨hz, ((hUF z).symm.trans hzx).symm⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hxz⟩, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, (hUF z).trans hxz.symm⟩

/-- A fibre on which the fine partition agrees with the coarse one is a single block. -/
theorem fibre_card_one (F U : SheetPartition d) (S : Finset (Fin d)) (x : Fin d) (hx : x ∈ S)
    (h : ∀ z ∈ S, U.Rel x z → F.Rel x z) :
    ((S.filter (U.Rel x)).image F.repr).card = 1 := by
  classical
  refine Finset.card_eq_one.mpr ⟨F.repr x, ?_⟩
  ext y
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨z, ⟨hz, hxz⟩, rfl⟩
    exact (h z hz hxz).symm
  · rintro rfl
    exact ⟨x, ⟨hx, rfl⟩, rfl⟩

/-- **Agreement preserves the count.** -/
theorem card_image_eq_of_agree (F U : SheetPartition d) (S : Finset (Fin d)) (hFU : F.Refines U)
    (h : ∀ x ∈ S, ∀ z ∈ S, U.Rel x z → F.Rel x z) :
    (S.image F.repr).card = (S.image U.repr).card := by
  rw [card_image_fibre F U S hFU (fun _ ↦ 1) (fun x hx ↦ fibre_card_one F U S x hx (h x hx))]
  simp

/-- **One coarse block split in two adds one to the count.** -/
theorem card_image_eq_succ (F U : SheetPartition d) (S : Finset (Fin d)) (hFU : F.Refines U)
    (r p q : Fin d) (hr : r ∈ S) (hp : p ∈ S) (hq : q ∈ S) (hrp : U.Rel r p) (hrq : U.Rel r q)
    (hpq : ¬ F.Rel p q) (hcover : ∀ z ∈ S, U.Rel r z → F.Rel p z ∨ F.Rel q z)
    (h : ∀ x ∈ S, ¬ U.Rel r x → ∀ z ∈ S, U.Rel x z → F.Rel x z) :
    (S.image F.repr).card = (S.image U.repr).card + 1 := by
  have hfib : ∀ x ∈ S, ((S.filter (U.Rel x)).image F.repr).card =
      (fun b ↦ if b = U.repr r then 2 else 1) (U.repr x) := by
    intro x hx
    by_cases hxr : U.Rel r x
    · have hb : U.repr x = U.repr r := hxr.symm
      simp only [hb, ite_true]
      have hEq : (S.filter (U.Rel x)).image F.repr = {F.repr p, F.repr q} := by
        ext y
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨z, ⟨hz, hxz⟩, rfl⟩
          rcases hcover z hz (hxr.trans hxz) with h1 | h1
          · exact Or.inl h1.symm
          · exact Or.inr h1.symm
        · rintro (rfl | rfl)
          · exact ⟨p, ⟨hp, hxr.symm.trans hrp⟩, rfl⟩
          · exact ⟨q, ⟨hq, hxr.symm.trans hrq⟩, rfl⟩
      rw [hEq, Finset.card_pair hpq]
    · have hb : U.repr x ≠ U.repr r := fun h' ↦ hxr h'.symm
      simp only [hb, ite_false]
      exact fibre_card_one F U S x hx (h x hx hxr)
  rw [card_image_fibre F U S hFU (fun b ↦ if b = U.repr r then 2 else 1) hfib]
  have hmem : U.repr r ∈ S.image U.repr := Finset.mem_image.mpr ⟨r, hr, rfl⟩
  rw [← Finset.add_sum_erase _ _ hmem, ite_eq_left rfl]
  rw [Finset.sum_congr rfl (fun b hb ↦ ite_eq_right (Finset.ne_of_mem_erase hb)),
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hmem]
  have : 0 < (S.image U.repr).card := Finset.card_pos.mpr ⟨_, hmem⟩
  omega

/-- The blocks inside a coarse block, when there are exactly two named ones. -/
theorem rel_or_rel_of_card_two (F : SheetPartition d) (S : Finset (Fin d))
    (hcard : (S.image F.repr).card = 2) (p q : Fin d) (hp : p ∈ S) (hq : q ∈ S)
    (hpq : ¬ F.Rel p q) (z : Fin d) (hz : z ∈ S) : F.Rel p z ∨ F.Rel q z := by
  classical
  have hsub : ({F.repr p, F.repr q} : Finset (Fin d)) ⊆ S.image F.repr := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hEq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_pair hpq])
  have hz' : F.repr z ∈ S.image F.repr := Finset.mem_image.mpr ⟨z, hz, rfl⟩
  rw [← hEq] at hz'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
  rcases hz' with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- **Moving one finite set onto another of the same size**, by a permutation supported in a
given set containing both. -/
theorem exists_perm_image (D : Fin d → Prop) (P Q : Finset (Fin d)) (hP : ∀ x ∈ P, D x)
    (hQ : ∀ x ∈ Q, D x) (hcard : P.card = Q.card) :
    ∃ π : Equiv.Perm (Fin d), (∀ x, ¬ D x → π x = x) ∧ (∀ x, D x → D (π x)) ∧
      ∀ x, (π x ∈ Q ↔ x ∈ P) := by
  classical
  let T := {x : Fin d // D x}
  have hc : Fintype.card {x : T // x.1 ∈ P} = Fintype.card {x : T // x.1 ∈ Q} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have hP' : (Finset.univ.filter fun x : T ↦ x.1 ∈ P).card = P.card := by
      rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
      congr 1
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨x, hx, hxy⟩ ↦ hxy ▸ hx, fun hy ↦ ⟨⟨y, hP y hy⟩, hy, rfl⟩⟩
    have hQ' : (Finset.univ.filter fun x : T ↦ x.1 ∈ Q).card = Q.card := by
      rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
      congr 1
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨x, hx, hxy⟩ ↦ hxy ▸ hx, fun hy ↦ ⟨⟨y, hQ y hy⟩, hy, rfl⟩⟩
    rw [hP', hQ', hcard]
  let e : {x : T // x.1 ∈ P} ≃ {x : T // x.1 ∈ Q} := Fintype.equivOfCardEq hc
  let σ : Equiv.Perm T := Equiv.extendSubtype e
  refine ⟨Equiv.Perm.ofSubtype σ, fun x hx ↦ Equiv.Perm.ofSubtype_apply_of_not_mem σ hx,
    fun x hx ↦ ?_, fun x ↦ ?_⟩
  · rw [Equiv.Perm.ofSubtype_apply_of_mem σ hx]
    exact (σ ⟨x, hx⟩).2
  · by_cases hx : D x
    · rw [Equiv.Perm.ofSubtype_apply_of_mem σ hx]
      constructor
      · intro h
        by_contra hxP
        exact Equiv.extendSubtype_not_mem e ⟨x, hx⟩ hxP h
      · intro h
        exact Equiv.extendSubtype_mem e ⟨x, hx⟩ h
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem σ hx]
      exact ⟨fun h ↦ (hx (hQ x h)).elim, fun h ↦ (hx (hP x h)).elim⟩

end Counting

/-! ## 2.  The incoming datum around the contracted occurrence -/

section Incoming

open ValencyThreeSplit

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)

/-- An occurrence's class lies in the class of a source vertex it is incident to. -/
theorem rel_of_incident {e : data.SourceEdge} {X : data.SourceVertex} (h : Incident data e X)
    (s : Fin degree) (hs : (data.edgePartition e.1.1).Rel e.1.2 s) :
    (data.vertexPartition X.1.1).Rel X.1.2 s := by
  obtain ⟨hT, hR⟩ := (incident_iff_target_mem_and_rel data e X).mp h
  exact hR.trans ((refines_of_mem_incidentEdges_local data hT).rel hs)

/-- An incident occurrence of full index is the whole vertex class. -/
theorem rel_iff_of_index {e : data.SourceEdge} {X : data.SourceVertex} (h : Incident data e X)
    (hcard : data.sourceEdgeIndex e = size data X) (s : Fin degree) :
    (data.edgePartition e.1.1).Rel e.1.2 s ↔ (data.vertexPartition X.1.1).Rel X.1.2 s := by
  have hsub : (data.edgePartition e.1.1).block e.1.2 ⊆
      (data.vertexPartition X.1.1).block X.1.2 := fun t ht ↦ by
    rw [SheetPartition.mem_block_iff] at ht ⊢
    exact rel_of_incident data h t ht
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    change (data.vertexPartition X.1.1).blockCard X.1.2 ≤
      (data.edgePartition e.1.1).blockCard e.1.2
    exact le_of_eq hcard.symm)
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff, heq]

/-- Two distinct occurrences over one target occurrence carry different classes. -/
theorem not_rel_of_ne {e f : data.SourceEdge} (hT : e.1.1 = f.1.1) (hne : e ≠ f) :
    ¬ (data.edgePartition e.1.1).Rel e.1.2 f.1.2 := by
  intro h
  apply hne
  apply Subtype.ext
  apply Prod.ext hT
  have he := e.2
  have hf := f.2
  change (data.edgePartition e.1.1).repr e.1.2 = e.1.2 at he
  change (data.edgePartition f.1.1).repr f.1.2 = f.1.2 at hf
  change (data.edgePartition e.1.1).repr e.1.2 = (data.edgePartition e.1.1).repr f.1.2 at h
  rw [← hT] at hf
  exact he.symm.trans (h.trans hf)

/-- Two incident occurrences over one target occurrence whose indices add up to the size of
the vertex split its class. -/
theorem rel_iff_of_two {e f : data.SourceEdge} {X : data.SourceVertex} (he : Incident data e X)
    (hf : Incident data f X) (hT : e.1.1 = f.1.1) (hne : e ≠ f)
    (hcard : data.sourceEdgeIndex e + data.sourceEdgeIndex f = size data X) (s : Fin degree) :
    (data.vertexPartition X.1.1).Rel X.1.2 s ↔
      (data.edgePartition e.1.1).Rel e.1.2 s ∨ (data.edgePartition e.1.1).Rel f.1.2 s := by
  classical
  set E := data.edgePartition e.1.1
  have hfE : ∀ t, (data.edgePartition f.1.1).Rel f.1.2 t ↔ E.Rel f.1.2 t := by
    intro t; rw [← hT]
  have hsub : E.block e.1.2 ∪ E.block f.1.2 ⊆ (data.vertexPartition X.1.1).block X.1.2 := by
    intro t ht
    rw [Finset.mem_union, SheetPartition.mem_block_iff, SheetPartition.mem_block_iff] at ht
    rw [SheetPartition.mem_block_iff]
    rcases ht with ht | ht
    · exact rel_of_incident data he t ht
    · exact rel_of_incident data hf t ((hfE t).mpr ht)
  have hdisj : Disjoint (E.block e.1.2) (E.block f.1.2) := by
    rw [Finset.disjoint_left]
    intro t h1 h2
    rw [SheetPartition.mem_block_iff] at h1 h2
    exact not_rel_of_ne data hT hne (h1.trans h2.symm)
  have hfcard : data.sourceEdgeIndex f = E.blockCard f.1.2 := by
    change (data.edgePartition f.1.1).blockCard f.1.2 = _
    rw [← hT]
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_union_of_disjoint hdisj]
    change (data.vertexPartition X.1.1).blockCard X.1.2 ≤ E.blockCard e.1.2 + E.blockCard f.1.2
    rw [← hfcard]
    exact le_of_eq hcard.symm)
  rw [← SheetPartition.mem_block_iff, ← heq, Finset.mem_union, SheetPartition.mem_block_iff,
    SheetPartition.mem_block_iff]

/-- **An unramified class over a divalent target vertex is one class of each occurrence
there.** -/
theorem block_eq_of_unram {u : target.V} (hu2 : (GluingDatum.incidentEdges u).card = 2)
    (s : Fin degree) (h0 : localRamificationAt data u s = 0) (e : target.edges)
    (he : e ∈ GluingDatum.incidentEdges u) :
    (data.edgePartition e).block s = (data.vertexPartition u).block s := by
  classical
  obtain ⟨e₁, e₂, hne, hEq⟩ := Finset.card_eq_two.mp hu2
  unfold localRamificationAt at h0
  rw [hu2, hEq, Finset.sum_pair hne] at h0
  have p1 := (data.edgePartition e₁).blockCountWithin_pos (data.vertexPartition u) s
  have p2 := (data.edgePartition e₂).blockCountWithin_pos (data.vertexPartition u) s
  have h1 : (data.edgePartition e).blockCountWithin (data.vertexPartition u) s = 1 := by
    rw [hEq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    push_cast at h0
    rcases he with rfl | rfl <;> omega
  exact (data.edgePartition e).block_eq_of_refines_of_blockCountWithin_eq_one _
    (refines_of_mem_incidentEdges_local data he) s h1

/-- Over a vertex of change one, every class but the ramified one is unramified. -/
theorem ram_zero_of_not_rel (hValid : data.Valid) {u : target.V}
    (hch : data.targetChange u = 1) (r s : Fin degree) (hr : localRamificationAt data u r = 1)
    (hrs : ¬ (data.vertexPartition u).Rel r s) : localRamificationAt data u s = 0 := by
  classical
  set Br := (data.vertexPartition u).toBlock r
  set Bs := (data.vertexPartition u).toBlock s
  have hne : Br ≠ Bs := fun h ↦ hrs (congrArg Subtype.val h)
  have hr' : data.localRamification u Br = 1 := by
    rw [← localRamificationAt_block]
    exact (localRamificationAt_congr data u ((data.vertexPartition u).rel_repr_left r)).trans hr
  have hs' : data.localRamification u Bs = localRamificationAt data u s := by
    rw [← localRamificationAt_block]
    exact localRamificationAt_congr data u ((data.vertexPartition u).rel_repr_left s)
  have hnn : ∀ B, 0 ≤ data.localRamification u B :=
    fun B ↦ data.localRamification_nonneg u (hValid.2 u) B
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := data.localRamification u)
    (Finset.subset_univ {Br, Bs}) (fun B _ _ ↦ hnn B)
  rw [Finset.sum_pair hne] at hle
  have htot : ∑ B, data.localRamification u B = 1 := hch
  have := hnn Bs
  rw [hs'] at this hle
  omega

variable {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b))

include hc in
/-- **The forest count at one merged class**, in the order `(u, v)`. -/
theorem forest_count (hForest : ContractionForest data a b contracted) {u v : target.V}
    (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a)) (s : Fin degree) :
    ((((mergedPartition data a b).block s).image (data.edgePartition contracted).repr).card : ℤ)
        + 1 =
      (((mergedPartition data a b).block s).image (data.vertexPartition u).repr).card +
        (((mergedPartition data a b).block s).image (data.vertexPartition v).repr).card := by
  have h := contractionForest_count data hc hForest ((mergedPartition data a b).toBlock s)
  have hb : (mergedPartition data a b).block ((mergedPartition data a b).toBlock s).1 =
      (mergedPartition data a b).block s :=
    (mergedPartition data a b).block_eq_of_rel ((mergedPartition data a b).rel_repr_left s)
  unfold SheetPartition.blockCountWithin at h
  rw [hb] at h
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · rw [h]; ring

end Incoming

/-! ## 3.  The incoming resolution on every merged class, in both pictures -/

section Pictures

open ValencyThreeSplit

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  {u v : target.V} (hForest : ContractionForest data a b contracted)
  (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a))

include huv in
theorem refines_merged_u : (data.vertexPartition u).Refines (mergedPartition data a b) := by
  rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact vertexPartition_refines_mergedPartition data _ _
  · exact vertexPartition_refines_mergedPartition_right data _ _

include huv in
theorem refines_merged_v : (data.vertexPartition v).Refines (mergedPartition data a b) := by
  rcases huv with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact vertexPartition_refines_mergedPartition_right data _ _
  · exact vertexPartition_refines_mergedPartition data _ _

include hc hab huv in
theorem contracted_refines_u : (data.edgePartition contracted).Refines (data.vertexPartition u) :=
  refines_of_mem_incidentEdges_local data
    (contracted_mem_incidentEdges hc (side_of_huv hab huv).1)

include hc hab huv in
theorem contracted_refines_v : (data.edgePartition contracted).Refines (data.vertexPartition v) :=
  refines_of_mem_incidentEdges_local data
    (contracted_mem_incidentEdges hc (side_of_huv hab huv).2.1)

include hc hab hForest huv in
/-- **One class on the trivalent side.**  Where the contracted occurrence's partition agrees
with the divalent side on a merged class, the trivalent side is the whole merged class. -/
theorem pv_eq_merged (s : Fin degree)
    (hagree : ∀ x ∈ (mergedPartition data a b).block s, ∀ z ∈ (mergedPartition data a b).block s,
      (data.vertexPartition u).Rel x z → (data.edgePartition contracted).Rel x z)
    (t : Fin degree) :
    (data.vertexPartition v).Rel s t ↔ (mergedPartition data a b).Rel s t := by
  have hc1 := card_image_eq_of_agree (data.edgePartition contracted) (data.vertexPartition u)
    ((mergedPartition data a b).block s) (contracted_refines_u data hc hab huv) hagree
  have hf := forest_count data hc hForest huv s
  have h1 : (data.vertexPartition v).blockCountWithin (mergedPartition data a b) s = 1 := by
    unfold SheetPartition.blockCountWithin
    rw [hc1] at hf
    omega
  have hb := (data.vertexPartition v).block_eq_of_refines_of_blockCountWithin_eq_one _
    (refines_merged_v data huv) s h1
  rw [← SheetPartition.mem_block_iff, hb, SheetPartition.mem_block_iff]

variable (hu2 : (GluingDatum.incidentEdges u).card = 2) (hchu : data.targetChange u = 1)

include fd hu2 hchu in
/-- **Every class over the divalent side but the ramified one is unramified**, hence one
class of each occurrence there. -/
theorem block_eq_off (r : Fin degree) (hr : localRamificationAt data u r = 1) (s : Fin degree)
    (hrs : ¬ (data.vertexPartition u).Rel r s) (e : target.edges)
    (he : e ∈ GluingDatum.incidentEdges u) :
    (data.edgePartition e).block s = (data.vertexPartition u).block s :=
  block_eq_of_unram data hu2 s (ram_zero_of_not_rel data fd.valid hchu r s hr hrs) e he

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem rel_iff_of_block_eq {P Q : SheetPartition degree} {s : Fin degree}
    (h : P.block s = Q.block s) (t : Fin degree) : P.Rel s t ↔ Q.Rel s t := by
  rw [← SheetPartition.mem_block_iff, h, SheetPartition.mem_block_iff]

include fd hc hab hForest huv hu2 hchu in
/-- **The incoming resolution in the two-vertex picture** (base tree `T₂`): the divalent side is
the moving direction's partition with the classes of `e₂` and `e₅` merged, the contracted
occurrence has the same classes, and the trivalent side is the merged partition. -/
theorem two_shape (P : TwoPicture data hc hab hOne block u v) {e0 e3 : data.SourceEdge}
    (h0 : e0 ∈ bdAt data contracted P.R) (h3 : e3 ∈ bdAt data contracted P.R) (hne : e0 ≠ e3) :
    (∀ s t, (data.vertexPartition u).Rel s t ↔ (data.edgePartition e0.1.1).Rel s t ∨
      (((data.edgePartition e0.1.1).Rel e0.1.2 s ∨ (data.edgePartition e0.1.1).Rel e3.1.2 s) ∧
        ((data.edgePartition e0.1.1).Rel e0.1.2 t ∨ (data.edgePartition e0.1.1).Rel e3.1.2 t))) ∧
    (∀ s t, (data.edgePartition contracted).Rel s t ↔ (data.vertexPartition u).Rel s t) ∧
    (∀ s t, (data.vertexPartition v).Rel s t ↔ (mergedPartition data a b).Rel s t) := by
  classical
  obtain ⟨huw, -, -⟩ := side_of_huv hab huv
  have hRu := P.R_over
  have hT03 : e0.1.1 = e3.1.1 := bdAt_target_eq_of_divalent data hc hRu huw hu2 h0 h3
  have hbd : bdAt data contracted P.R = {e0, e3} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact h0
      · exact h3
    · rw [P.card_bdAt_R, Finset.card_pair hne]
  obtain ⟨hr1a, hr1b⟩ := P.r1 fd huv hu2
  rw [hbd, Finset.sum_pair hne] at hr1b
  have inc0 := ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp h0).1).2
  have inc3 := ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp h3).1).2
  have hR := rel_iff_of_two data inc0 inc3 hT03 hne (by exact_mod_cast hr1b)
  have he₁t : P.e₁.1.1 = contracted := by
    have h := (mem_ndOver data _ _ _).mp (P.ndOver_R ▸ Finset.mem_singleton_self P.e₁)
    exact h.2
  have hE1 := rel_iff_of_index data ((mem_ndAt data _ _).mp P.e₁_R).2 (by exact_mod_cast hr1a)
  rw [he₁t, hRu] at hE1
  rw [hRu] at hR
  have hT : e0.1.1 ∈ GluingDatum.incidentEdges u := by
    have h := target_mem_incidentEdges data inc0
    rwa [hRu] at h
  have hramR : localRamificationAt data u P.R.1.2 = 1 := by
    have h : localRamificationAt data P.R.1.1 P.R.1.2 = 1 := P.R_ram
    rwa [hRu] at h
  have hoff := block_eq_off data fd hu2 hchu P.R.1.2 hramR
  have hcu := contracted_mem_incidentEdges hc huw
  -- the contracted occurrence and the divalent side agree everywhere
  have hPt : ∀ s t, (data.edgePartition contracted).Rel s t ↔ (data.vertexPartition u).Rel s t := by
    intro s t
    by_cases hs : (data.vertexPartition u).Rel P.R.1.2 s
    · have hs' := (hE1 s).mpr hs
      constructor
      · intro h
        exact hs.symm.trans ((hE1 t).mp (hs'.trans h))
      · intro h
        exact hs'.symm.trans ((hE1 t).mpr (hs.trans h))
    · exact rel_iff_of_block_eq (hoff s hs contracted hcu) t
  refine ⟨?_, hPt, fun s t ↦ pv_eq_merged data hc hab hForest huv s
    (fun x _ z _ h ↦ (hPt x z).mpr h) t⟩
  intro s t
  by_cases hs : (data.vertexPartition u).Rel P.R.1.2 s
  · have hs0 := (hR s).mp hs
    constructor
    · intro h
      have := (hR t).mp (hs.trans h)
      exact Or.inr ⟨hs0, this⟩
    · rintro (h | ⟨-, h⟩)
      · have hRt : (data.vertexPartition u).Rel P.R.1.2 t := by
          rcases hs0 with h' | h'
          · exact (hR t).mpr (Or.inl (h'.trans h))
          · exact (hR t).mpr (Or.inr (h'.trans h))
        exact hs.symm.trans hRt
      · have : (data.vertexPartition u).Rel P.R.1.2 t := (hR t).mpr h
        exact hs.symm.trans this
  · have hsE := rel_iff_of_block_eq (hoff s hs e0.1.1 hT) t
    have hn : ¬ ((data.edgePartition e0.1.1).Rel e0.1.2 s ∨
        (data.edgePartition e0.1.1).Rel e3.1.2 s) := by
      intro h
      apply hs
      exact (hR s).mpr h
    constructor
    · intro h; exact Or.inl (hsE.mpr h)
    · rintro (h | ⟨h, -⟩)
      · exact hsE.mp h
      · exact (hn h).elim

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Two source vertices over one target vertex that are related are equal. -/
theorem sourceVertex_eq_of_rel {X Y : data.SourceVertex} (hXY : X.1.1 = Y.1.1)
    (h : (data.vertexPartition X.1.1).Rel X.1.2 Y.1.2) : X = Y := by
  apply Subtype.ext
  apply Prod.ext hXY
  have hX := X.2
  have hY := Y.2
  change (data.vertexPartition X.1.1).repr X.1.2 = X.1.2 at hX
  change (data.vertexPartition Y.1.1).repr Y.1.2 = Y.1.2 at hY
  change (data.vertexPartition X.1.1).repr X.1.2 = (data.vertexPartition X.1.1).repr Y.1.2 at h
  rw [← hXY] at hY
  exact hX.symm.trans (h.trans hY)

include fd hc hab hForest huv hu2 hchu in
/-- **The incoming resolution in the three-vertex picture** (base tree `T_α`): the divalent
side is the moving direction's partition, the trivalent side splits the anchor class into the
class `A'` of `e_δ` and the rest, and the contracted occurrence is their common refinement.
`A'` lies inside `A_u` and dangles above every other direction at the trivalent side. -/
theorem three_shape (P : ThreePicture data hc hab hOne block u v) {eα eδ : data.SourceEdge}
    (hα : eα ∈ bdAt data contracted P.R) (hδ : eδ ∈ bdAt data contracted P.Z) :
    (∀ s t, (data.vertexPartition u).Rel s t ↔ (data.edgePartition eα.1.1).Rel s t) ∧
    (∀ s t, (data.vertexPartition v).Rel s t ↔ (mergedPartition data a b).Rel s t ∧
      ((mergedPartition data a b).Rel block.1 s →
        ((data.edgePartition eδ.1.1).Rel eδ.1.2 s ↔ (data.edgePartition eδ.1.1).Rel eδ.1.2 t))) ∧
    (∀ s t, (data.edgePartition contracted).Rel s t ↔
      (data.vertexPartition u).Rel s t ∧ (data.vertexPartition v).Rel s t) ∧
    (∀ s, (data.edgePartition eδ.1.1).Rel eδ.1.2 s → (data.edgePartition eα.1.1).Rel eα.1.2 s) ∧
    (mergedPartition data a b).Rel block.1 eδ.1.2 ∧
    (∀ s, (data.edgePartition eδ.1.1).Rel eδ.1.2 s → ∀ e ∈ GluingDatum.incidentEdges v,
      e ≠ contracted → e ≠ eδ.1.1 → IsDangling data (data.sourceEdge e s)) := by
  classical
  obtain ⟨huw, -, -⟩ := side_of_huv hab huv
  have hRu := P.R_over
  have hZv := P.Z_over
  have hYv := P.Y_over
  have hbdR : bdAt data contracted P.R = {eα} := by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp P.card_bdAt_R
    rw [hx] at hα ⊢
    rw [Finset.mem_singleton.mp hα]
  have hbdZ : bdAt data contracted P.Z = {eδ} := by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp P.card_bdAt_Z
    rw [hx] at hδ ⊢
    rw [Finset.mem_singleton.mp hδ]
  obtain ⟨hr1a, hr1b⟩ := P.r1 fd
  obtain ⟨hr0a, hr0b⟩ := P.r0_Z fd
  rw [hbdR, Finset.sum_singleton] at hr1b
  rw [hbdZ, Finset.sum_singleton] at hr0b
  have incα := ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp hα).1).2
  have incδ := ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp hδ).1).2
  have inc₁ := ((mem_ndAt data _ _).mp P.e₁_R).2
  have inc' := ((mem_ndAt data _ _).mp P.e'_R).2
  have inc'Z := ((mem_ndAt data _ _).mp P.e'_Z).2
  have hRα := rel_iff_of_index data incα (by exact_mod_cast hr1b)
  have hRt := rel_iff_of_two data inc₁ inc' (P.e₁_target.trans P.e'_target.symm) P.e₁_ne
    (by exact_mod_cast hr1a)
  have hZe' := rel_iff_of_index data inc'Z (by exact_mod_cast hr0a)
  have hZδ := rel_iff_of_index data incδ (by exact_mod_cast hr0b)
  have hpq := not_rel_of_ne data (P.e₁_target.trans P.e'_target.symm) P.e₁_ne
  rw [P.e₁_target] at hRt hpq
  rw [P.e'_target] at hZe'
  rw [hRu] at hRα hRt
  rw [hZv] at hZe' hZδ
  have hTα : eα.1.1 ∈ GluingDatum.incidentEdges u := by
    have h := target_mem_incidentEdges data incα
    rwa [hRu] at h
  have hramR : localRamificationAt data u P.R.1.2 = 1 := by
    have h : localRamificationAt data P.R.1.1 P.R.1.2 = 1 := P.R_ram
    rwa [hRu] at h
  have hoff := block_eq_off data fd hu2 hchu P.R.1.2 hramR
  have hcu := contracted_mem_incidentEdges hc huw
  set Pu := data.vertexPartition u
  set Pv := data.vertexPartition v
  set Pt := data.edgePartition contracted
  have hPtoff : ∀ s, ¬ Pu.Rel P.R.1.2 s → ∀ t, Pt.Rel s t ↔ Pu.Rel s t :=
    fun s hs ↦ rel_iff_of_block_eq (hoff s hs contracted hcu)
  have hPu : ∀ s t, Pu.Rel s t ↔ (data.edgePartition eα.1.1).Rel s t := by
    intro s t
    by_cases hs : Pu.Rel P.R.1.2 s
    · have hs' := (hRα s).mpr hs
      constructor
      · intro h
        exact hs'.symm.trans ((hRα t).mpr (hs.trans h))
      · intro h
        exact hs.symm.trans ((hRα t).mp (hs'.trans h))
    · exact (rel_iff_of_block_eq (hoff s hs eα.1.1 hTα) t).symm
  -- the count on the anchor class
  set S := (mergedPartition data a b).block block.1
  have hsubR := block_subset_of_mem_fib data hc hab hOne block P.R_mem
  have hsubZ := block_subset_of_mem_fib data hc hab hOne block P.Z_mem
  have hsubY := block_subset_of_mem_fib data hc hab hOne block P.Y_mem
  rw [hRu] at hsubR
  rw [hZv] at hsubZ
  rw [hYv] at hsubY
  have inS_R : ∀ x, Pu.Rel P.R.1.2 x → x ∈ S := fun x hx ↦
    hsubR ((SheetPartition.mem_block_iff _ _ _).mpr hx)
  have inS_Z : ∀ x, Pv.Rel P.Z.1.2 x → x ∈ S := fun x hx ↦
    hsubZ ((SheetPartition.mem_block_iff _ _ _).mpr hx)
  have inS_Y : ∀ x, Pv.Rel P.Y.1.2 x → x ∈ S := fun x hx ↦
    hsubY ((SheetPartition.mem_block_iff _ _ _).mpr hx)
  have hp1 : Pu.Rel P.R.1.2 P.e₁.1.2 := (hRt _).mpr (Or.inl rfl)
  have hq1 : Pu.Rel P.R.1.2 P.e'.1.2 := (hRt _).mpr (Or.inr rfl)
  have hsucc := card_image_eq_succ Pt Pu S (contracted_refines_u data hc hab huv) P.R.1.2
    P.e₁.1.2 P.e'.1.2 (inS_R _ rfl) (inS_R _ hp1) (inS_R _ hq1) hp1 hq1 hpq
    (fun z _ hz ↦ (hRt z).mp hz)
    (fun x _ hx z _ hxz ↦ (hPtoff x hx z).mpr hxz)
  have hf := forest_count data hc hForest huv block.1
  have hcv2 : (S.image Pv.repr).card = 2 := by
    change ((S.image Pt.repr).card : ℤ) + 1 = (S.image Pu.repr).card + (S.image Pv.repr).card
      at hf
    rw [hsucc] at hf
    push_cast at hf
    omega
  have hZY : ¬ Pv.Rel P.Z.1.2 P.Y.1.2 := by
    intro h
    apply P.Y_ne_Z
    symm
    apply sourceVertex_eq_of_rel data (hZv.trans hYv.symm)
    rw [hZv]
    exact h
  have hZorY := rel_or_rel_of_card_two Pv S hcv2 P.Z.1.2 P.Y.1.2 (inS_Z _ rfl) (inS_Y _ rfl) hZY
  have hPtZ : ∀ x, Pt.Rel P.e'.1.2 x ↔ Pv.Rel P.Z.1.2 x := hZe'
  have hZsubR : ∀ x, Pv.Rel P.Z.1.2 x → Pu.Rel P.R.1.2 x :=
    fun x hx ↦ (hRt x).mpr (Or.inr ((hPtZ x).mpr hx))
  have hPv : ∀ s t, Pv.Rel s t ↔ (mergedPartition data a b).Rel s t ∧
      ((mergedPartition data a b).Rel block.1 s → ((data.edgePartition eδ.1.1).Rel eδ.1.2 s ↔
        (data.edgePartition eδ.1.1).Rel eδ.1.2 t)) := by
    intro s t
    by_cases hsA : (mergedPartition data a b).Rel block.1 s
    · have hsS : s ∈ S := (SheetPartition.mem_block_iff _ _ _).mpr hsA
      constructor
      · intro h
        refine ⟨(refines_merged_v data huv).rel h, fun _ ↦ ?_⟩
        rw [hZδ, hZδ]
        exact ⟨fun h' ↦ h'.trans h, fun h' ↦ h'.trans h.symm⟩
      · rintro ⟨hW, hiff⟩
        have htS : t ∈ S := (SheetPartition.mem_block_iff _ _ _).mpr (hsA.trans hW)
        have hiff' := hiff hsA
        rw [hZδ, hZδ] at hiff'
        by_cases hZs : Pv.Rel P.Z.1.2 s
        · exact hZs.symm.trans (hiff'.mp hZs)
        · have hYs := (hZorY s hsS).resolve_left hZs
          have hZt : ¬ Pv.Rel P.Z.1.2 t := fun h' ↦ hZs (hiff'.mpr h')
          have hYt := (hZorY t htS).resolve_left hZt
          exact hYs.symm.trans hYt
    · have hag : ∀ x ∈ (mergedPartition data a b).block s, ∀ z ∈ (mergedPartition data a b).block s, Pu.Rel x z → Pt.Rel x z := by
        intro x hx z _ hxz
        have hxR : ¬ Pu.Rel P.R.1.2 x := by
          intro hR'
          apply hsA
          have h1 : (mergedPartition data a b).Rel block.1 x := (SheetPartition.mem_block_iff _ _ _).mp (inS_R x hR')
          exact h1.trans ((SheetPartition.mem_block_iff _ _ _).mp hx).symm
        exact (hPtoff x hxR z).mpr hxz
      rw [pv_eq_merged data hc hab hForest huv s hag t]
      exact ⟨fun h ↦ ⟨h, fun h' ↦ (hsA h').elim⟩, fun h ↦ h.1⟩
  refine ⟨hPu, hPv, ?_, ?_, ?_, ?_⟩
  · intro s t
    constructor
    · intro h
      exact ⟨(contracted_refines_u data hc hab huv).rel h,
        (contracted_refines_v data hc hab huv).rel h⟩
    · rintro ⟨hu, hv⟩
      by_cases hs : Pu.Rel P.R.1.2 s
      · have hsA : (mergedPartition data a b).Rel block.1 s := (SheetPartition.mem_block_iff _ _ _).mp (inS_R s hs)
        have hZiff := ((hPv s t).mp hv).2 hsA
        rw [hZδ, hZδ] at hZiff
        rcases (hRt s).mp hs with h1 | h1
        · have hZs : ¬ Pv.Rel P.Z.1.2 s := fun h' ↦ hpq (h1.trans ((hPtZ s).mpr h').symm)
          have hZt : ¬ Pv.Rel P.Z.1.2 t := fun h' ↦ hZs (hZiff.mpr h')
          rcases (hRt t).mp (hs.trans hu) with h2 | h2
          · exact h1.symm.trans h2
          · exact (hZt ((hPtZ t).mp h2)).elim
        · have hZs := (hPtZ s).mp h1
          exact h1.symm.trans ((hPtZ t).mpr (hZiff.mp hZs))
      · exact (hPtoff s hs t).mpr hu
  · intro s hs
    exact (hRα s).mpr (hZsubR s ((hZδ s).mp hs))
  · exact (SheetPartition.mem_block_iff _ _ _).mp (inS_Z _ ((hZδ _).mp rfl))
  · intro s hs e he hec heδ
    by_contra hnd
    have hZs := (hZδ s).mp hs
    have hinc : Incident data (data.sourceEdge e s) P.Z := by
      apply (incident_iff_target_mem_and_rel data _ _).mpr
      refine ⟨by rw [hZv]; exact he, ?_⟩
      rw [hZv]
      exact hZs.trans ((refines_of_mem_incidentEdges_local data he).rel
        ((data.edgePartition e).rel_repr_right s))
    have hmem : data.sourceEdge e s ∈ ndAt data P.Z := (mem_ndAt data _ _).mpr ⟨hnd, hinc⟩
    have hδZ : eδ ∈ ndAt data P.Z := ((mem_bdAt data _ _).mp hδ).1
    have hne' : P.e' ≠ eδ := fun h ↦ ((mem_bdAt data _ _).mp hδ).2 (h ▸ P.e'_target)
    have hnd2 : (ndAt data P.Z).card = 2 := by rw [card_ndAt]; exact P.Z_nd
    have hEq : ndAt data P.Z = {P.e', eδ} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact P.e'_Z
        · exact hδZ
      · rw [hnd2, Finset.card_pair hne']
    rw [hEq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact hec ((congrArg (fun x : data.SourceEdge ↦ x.1.1) h).trans P.e'_target)
    · exact heδ (congrArg (fun x : data.SourceEdge ↦ x.1.1) h)

end Pictures

/-! ## 4.  Transports between two regrowths' resolutions (limit coordinates) -/

section LimitTransport

open ResolutionExpansionFree
open ResolutionM11 (LocalResolution)
open W3Nd2SourceCandidates (rightOf)
open W3Nd2StarExhaustionProof (edge_rel_iff edgePerm_agree agree_symm_apply rightOf_pullback
  rightOf_eq_false incident_iff)

/-- Two classes of a partition merged into one, as a relation.

As an interface: a relation shaper, the relation of `SheetPartition.mergeBlocks`
(`mergeBlocks_rel_iff` of `W3ShiftStarExhaustionProof`) without its separation hypothesis;
consumed by `transportFree_two` and produced by `cover_two`. -/
def MergeRel {d : ℕ} (E : SheetPartition d) (m₀ m₃ s t : Fin d) : Prop :=
  E.Rel s t ∨ ((E.Rel m₀ s ∨ E.Rel m₃ s) ∧ (E.Rel m₀ t ∨ E.Rel m₃ t))

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  (ψ : GeometricDatumIso first second) {wall : target₁.V} {wall' : target₂.V}
  (hWall : ψ.targetVertex wall = wall')

theorem mergeRel_map (U : target₁.edges) (m₀ m₃ m₀' m₃' : Fin degree)
    (h0 : (second.edgePartition (ψ.targetEdge U)).Rel (ψ.edgePerm U m₀) m₀')
    (h3 : (second.edgePartition (ψ.targetEdge U)).Rel (ψ.edgePerm U m₃) m₃') (s t : Fin degree) :
    MergeRel (first.edgePartition U) m₀ m₃ s t ↔
      MergeRel (second.edgePartition (ψ.targetEdge U)) m₀' m₃' (ψ.edgePerm U s)
        (ψ.edgePerm U t) := by
  have hm : ∀ (m m' : Fin degree),
      (second.edgePartition (ψ.targetEdge U)).Rel (ψ.edgePerm U m) m' → ∀ z,
      ((first.edgePartition U).Rel m z ↔
        (second.edgePartition (ψ.targetEdge U)).Rel m' (ψ.edgePerm U z)) := by
    intro m m' h z
    rw [edge_rel_iff ψ U]
    exact ⟨fun h' ↦ h.symm.trans h', fun h' ↦ h.trans h'⟩
  unfold MergeRel
  rw [edge_rel_iff ψ U, hm _ _ h0, hm _ _ h0, hm _ _ h3, hm _ _ h3]

theorem ends_of_mem {T : CFGraph} {v : T.V} {e : T.edges}
    (h : e ∈ GluingDatum.incidentEdges v) :
    (e : T.V × T.V).1 = v ∨ (e : T.V × T.V).2 = v := by
  simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem mem_of_ends {T : CFGraph} {v : T.V} {e : T.edges}
    (h : (e : T.V × T.V).1 = v ∨ (e : T.V × T.V).2 = v) :
    e ∈ GluingDatum.incidentEdges v := by
  simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using h

include hWall in
/-- **The transport in the two-vertex picture**: one permutation, the moving direction's,
carries all three partitions, and no coherence is needed. -/
theorem transportFree_two (U : target₁.edges) (hU : U ∈ GluingDatum.incidentEdges wall)
    (U' : target₂.edges) (hU'e : ψ.targetEdge U = U')
    (res res' : LocalResolution degree) (m₀ m₃ m₀' m₃' : Fin degree)
    (hL : ∀ s t, res.left.Rel s t ↔ MergeRel (first.edgePartition U) m₀ m₃ s t)
    (hL' : ∀ s t, res'.left.Rel s t ↔
      MergeRel (second.edgePartition (U')) m₀' m₃' s t)
    (hN : ∀ s t, res.newEdge.Rel s t ↔ res.left.Rel s t)
    (hN' : ∀ s t, res'.newEdge.Rel s t ↔ res'.left.Rel s t)
    (hR : ∀ s t, res.right.Rel s t ↔ (first.vertexPartition wall).Rel s t)
    (hR' : ∀ s t, res'.right.Rel s t ↔ (second.vertexPartition wall').Rel s t)
    (hLref : res.left.Refines (first.vertexPartition wall))
    (h0 : (second.edgePartition (U')).Rel (ψ.edgePerm U m₀) m₀')
    (h3 : (second.edgePartition (U')).Rel (ψ.edgePerm U m₃) m₃') :
    Nonempty (TransportFree ψ wall wall' (rightOf U) (rightOf (U')) res res') := by
  subst hU'e
  set σ := ψ.edgePerm U
  have hU' : ψ.targetEdge U ∈ GluingDatum.incidentEdges wall' :=
    (incident_iff ψ hWall U).mp (ends_of_mem hU)
  have hσ := edgePerm_agree ψ hWall U hU'
  have hWσ := M11StarExhaustionProof.wall_rel_iff_of_agree ψ hWall σ hσ
  have hLmap : ∀ a b, res.left.Rel a b ↔ res'.left.Rel (σ a) (σ b) := by
    intro a b
    rw [hL, hL']
    exact mergeRel_map ψ U m₀ m₃ m₀' m₃' h0 h3 a b
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel ψ wall wall' (rightOf U) _ res res'
    hWall (fun edge ↦ by rw [rightOf_pullback, Equiv.symm_apply_apply]) hLref
    (fun a b h ↦ (hR a b).mp h) σ σ σ hσ hσ hLmap ?_ ?_ ?_ ?_ ?_
  · intro a b; rw [hR, hR']; exact hWσ a b
  · intro a b; rw [hN, hN']; exact hLmap a b
  · intro s; rw [Equiv.symm_apply_apply]; rfl
  · intro s; rw [Equiv.symm_apply_apply]; rfl
  · intro edge hInc s
    by_cases hr : rightOf U edge = true
    · rw [ite_eq_left hr, ite_eq_left hr, hR]
      exact agree_symm_apply ψ σ _ hσ (edgePerm_agree ψ hWall edge
        ((incident_iff ψ hWall edge).mp hInc)) s
    · rw [ite_eq_right hr, ite_eq_right hr]
      have hEq : edge = U := rightOf_eq_false (by simpa using hr)
      subst hEq
      rw [Equiv.symm_apply_apply]; rfl

include hWall in
/-- A permutation agreeing with the wall's reads the anchor class. -/
theorem anchor_iff (A A' : Fin degree)
    (hA : (second.vertexPartition wall').Rel A' (ψ.vertexPerm wall A)) (τ : Equiv.Perm (Fin degree))
    (hτ : ∀ s, (first.vertexPartition wall).Rel ((ψ.vertexPerm wall).symm (τ s)) s)
    (s : Fin degree) :
    (first.vertexPartition wall).Rel A s ↔ (second.vertexPartition wall').Rel A' (τ s) := by
  have hV : ∀ x y, (first.vertexPartition wall).Rel x y ↔
      (second.vertexPartition wall').Rel (ψ.vertexPerm wall x) (ψ.vertexPerm wall y) := by
    intro x y
    rw [M11StarExhaustionProof.wall_rel_iff ψ hWall, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
  have hτV : (second.vertexPartition wall').Rel (τ s) (ψ.vertexPerm wall s) := by
    rw [M11StarExhaustionProof.wall_rel_iff ψ hWall, Equiv.symm_apply_apply]
    exact hτ s
  rw [hV]
  exact ⟨fun h ↦ hA.trans (h.trans hτV.symm), fun h ↦ hA.symm.trans (h.trans hτV)⟩

include hWall in
/-- **The transport in the three-vertex picture.**  The divalent side uses the moving
direction's permutation, the trivalent side `e_δ`'s, and the contracted occurrence the moving
direction's corrected inside `A_u` so that `A'` goes to `A'`.  It needs the third direction to
carry `A'` onto `A'` (`hX`). -/
theorem transportFree_three (U Δ X : target₁.edges)
    (hEdges : ∀ e, e ∈ GluingDatum.incidentEdges wall ↔ e = U ∨ e = Δ ∨ e = X)
    (hUΔ : U ≠ Δ) (hUX : U ≠ X) (U' Δ' : target₂.edges) (hU'e : ψ.targetEdge U = U')
    (hΔ'e : ψ.targetEdge Δ = Δ')
    (res res' : LocalResolution degree) (A A' mα mδ mα' mδ' : Fin degree)
    (hL : ∀ s t, res.left.Rel s t ↔ (first.edgePartition U).Rel s t)
    (hR : ∀ s t, res.right.Rel s t ↔ (first.vertexPartition wall).Rel s t ∧
      ((first.vertexPartition wall).Rel A s →
        ((first.edgePartition Δ).Rel mδ s ↔ (first.edgePartition Δ).Rel mδ t)))
    (hN : ∀ s t, res.newEdge.Rel s t ↔ res.left.Rel s t ∧ res.right.Rel s t)
    (hZR : ∀ s, (first.edgePartition Δ).Rel mδ s → (first.edgePartition U).Rel mα s)
    (hL' : ∀ s t, res'.left.Rel s t ↔ (second.edgePartition (U')).Rel s t)
    (hR' : ∀ s t, res'.right.Rel s t ↔ (second.vertexPartition wall').Rel s t ∧
      ((second.vertexPartition wall').Rel A' s →
        ((second.edgePartition (Δ')).Rel mδ' s ↔
          (second.edgePartition (Δ')).Rel mδ' t)))
    (hN' : ∀ s t, res'.newEdge.Rel s t ↔ res'.left.Rel s t ∧ res'.right.Rel s t)
    (hZR' : ∀ s, (second.edgePartition (Δ')).Rel mδ' s →
      (second.edgePartition (U')).Rel mα' s)
    (hA : (second.vertexPartition wall').Rel A' (ψ.vertexPerm wall A))
    (hmα : (second.edgePartition (U')).Rel (ψ.edgePerm U mα) mα')
    (hmδ : (second.edgePartition (Δ')).Rel (ψ.edgePerm Δ mδ) mδ')
    (hX : ∀ s, (first.vertexPartition wall).Rel A s →
      ((first.edgePartition Δ).Rel mδ s ↔
        (second.edgePartition (Δ')).Rel mδ' (ψ.edgePerm X s))) :
    Nonempty (TransportFree ψ wall wall' (rightOf U) (rightOf (U')) res res') := by
  subst hU'e hΔ'e
  classical
  set W := first.vertexPartition wall
  set W' := second.vertexPartition wall'
  set EU := first.edgePartition U
  set EΔ := first.edgePartition Δ
  set EU' := second.edgePartition (ψ.targetEdge U)
  set EΔ' := second.edgePartition (ψ.targetEdge Δ)
  set σ := ψ.edgePerm U
  set ρ := ψ.edgePerm Δ
  have memU := (hEdges U).mpr (Or.inl rfl)
  have memΔ := (hEdges Δ).mpr (Or.inr (Or.inl rfl))
  have hU' : ψ.targetEdge U ∈ GluingDatum.incidentEdges wall' :=
    (incident_iff ψ hWall U).mp (ends_of_mem memU)
  have hΔ' : ψ.targetEdge Δ ∈ GluingDatum.incidentEdges wall' :=
    (incident_iff ψ hWall Δ).mp (ends_of_mem memΔ)
  have hσ := edgePerm_agree ψ hWall U hU'
  have hρ := edgePerm_agree ψ hWall Δ hΔ'
  have hZmap : ∀ x, EΔ.Rel mδ x ↔ EΔ'.Rel mδ' (ρ x) := by
    intro x
    rw [edge_rel_iff ψ Δ]
    exact ⟨fun h ↦ hmδ.symm.trans h, fun h ↦ hmδ.trans h⟩
  -- the correction inside `A_u`
  set P := (Finset.univ.filter fun x ↦ EΔ.Rel mδ x).image σ
  set Q := Finset.univ.filter fun x ↦ EΔ'.Rel mδ' x
  have hQ : Q = (Finset.univ.filter fun x ↦ EΔ.Rel mδ x).image ρ := by
    ext y
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨ρ.symm y, (hZmap _).mpr (by rw [Equiv.apply_symm_apply]; exact h),
        Equiv.apply_symm_apply _ _⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hZmap x).mp hx
  have hcard : P.card = Q.card := by
    rw [hQ, Finset.card_image_of_injective _ σ.injective,
      Finset.card_image_of_injective _ ρ.injective]
  have hPD : ∀ y ∈ P, EU'.Rel mα' y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hx' : EΔ.Rel mδ x := by simpa using hx
    exact hmα.symm.trans ((edge_rel_iff ψ U mα x).mp (hZR x hx'))
  have hQD : ∀ y ∈ Q, EU'.Rel mα' y := by
    intro y hy
    exact hZR' y (by simpa [Q] using hy)
  obtain ⟨π, hπ, hπD, hπQ⟩ := exists_perm_image (fun y ↦ EU'.Rel mα' y) P Q hPD hQD hcard
  set τN : Equiv.Perm (Fin degree) := σ.trans π
  have hτU : ∀ s, EU'.Rel (τN s) (σ s) := by
    intro s
    change EU'.Rel (π (σ s)) (σ s)
    by_cases hD : EU'.Rel mα' (σ s)
    · exact (hπD _ hD).symm.trans hD
    · rw [hπ _ hD]; rfl
  have hτZ : ∀ s, EΔ'.Rel mδ' (τN s) ↔ EΔ.Rel mδ s := by
    intro s
    have h := hπQ (σ s)
    simp only [Q, P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at h
    change EΔ'.Rel mδ' (π (σ s)) ↔ _
    rw [h]
    exact ⟨fun ⟨x, hx, hxs⟩ ↦ σ.injective hxs ▸ hx, fun h' ↦ ⟨s, h', rfl⟩⟩
  have hUref := StableLocalProperties.refines_of_mem_incidentEdges second hU'
  have hτN := W3ShiftStarExhaustionProof.agree_of_rel ψ hWall σ τN hσ
    (fun s ↦ hUref.rel (hτU s))
  have hWσ := M11StarExhaustionProof.wall_rel_iff_of_agree ψ hWall σ hσ
  have hWρ := M11StarExhaustionProof.wall_rel_iff_of_agree ψ hWall ρ hρ
  have hWN := M11StarExhaustionProof.wall_rel_iff_of_agree ψ hWall τN hτN
  have hAρ := anchor_iff ψ hWall A A' hA ρ hρ
  have hAN := anchor_iff ψ hWall A A' hA τN hτN
  have hPU := edge_rel_iff ψ U
  have hLmap : ∀ a b, res.left.Rel a b ↔ res'.left.Rel (σ a) (σ b) := by
    intro a b; rw [hL, hL']; exact hPU a b
  have hRmap : ∀ a b, res.right.Rel a b ↔ res'.right.Rel (ρ a) (ρ b) := by
    intro a b
    rw [hR, hR', hWρ, hAρ, hZmap, hZmap]
  have hLN : ∀ a b, res.left.Rel a b ↔ res'.left.Rel (τN a) (τN b) := by
    intro a b
    rw [hL, hL', hPU]
    exact ⟨fun h ↦ (hτU a).trans (h.trans (hτU b).symm),
      fun h ↦ (hτU a).symm.trans (h.trans (hτU b))⟩
  have hRN : ∀ a b, res.right.Rel a b ↔ res'.right.Rel (τN a) (τN b) := by
    intro a b
    rw [hR, hR', hWN, hAN, hτZ, hτZ]
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel ψ wall wall' (rightOf U) _ res res'
    hWall (fun edge ↦ by rw [rightOf_pullback, Equiv.symm_apply_apply])
    (fun a b h ↦ (StableLocalProperties.refines_of_mem_incidentEdges first memU).rel
      ((hL a b).mp h)) (fun a b h ↦ ((hR a b).mp h).1) σ ρ τN hσ hρ hLmap hRmap
    ?_ ?_ ?_ ?_
  · intro a b; rw [hN, hN', hLN, hRN]
  · intro s
    rw [hL, hPU, Equiv.apply_symm_apply]
    exact hτU s
  · intro s
    have hAg := agree_symm_apply ψ ρ τN hρ hτN s
    rw [hR]
    refine ⟨hAg, fun _ ↦ ?_⟩
    rw [hZmap, Equiv.apply_symm_apply, hτZ]
  · intro edge hInc s
    have hmem := mem_of_ends hInc
    rcases (hEdges edge).mp hmem with rfl | rfl | rfl
    · have hr : rightOf edge edge = false := by simp [rightOf]
      rw [ite_eq_right (by rw [hr]; exact Bool.false_ne_true), ite_eq_right (by rw [hr]; exact Bool.false_ne_true),
        Equiv.symm_apply_apply]
      rfl
    · have hr : rightOf U edge = true := by simp [rightOf, Ne.symm hUΔ]
      rw [ite_eq_left hr, ite_eq_left hr, Equiv.symm_apply_apply]
      rfl
    · have hr : rightOf U edge = true := by simp [rightOf, Ne.symm hUX]
      rw [ite_eq_left hr, ite_eq_left hr, hR]
      have hmemX' : ψ.targetEdge edge ∈ GluingDatum.incidentEdges wall' :=
        (incident_iff ψ hWall edge).mp hInc
      have hAg := agree_symm_apply ψ ρ _ hρ (edgePerm_agree ψ hWall edge hmemX') s
      refine ⟨hAg, fun hA₀ ↦ ?_⟩
      have hAs : W.Rel A s := hA₀.trans hAg
      rw [hZmap, Equiv.apply_symm_apply]
      exact (hX s hAs).symm

end LimitTransport

/-! ## 5.  Re-choosing the limit isomorphism on one pendant branch -/

section PendantRealign

open TargetBranchRegion DanglingSideStructure
open DraismaVargas.Count.WallStar (Regrowth)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open W3Nd2StarExhaustionProof (Pendant pendantIso branchPerm farEnd farEnd_ne
  edgeMoved_self edgeMoved_other exists_branch_cut mem_side_of_moved)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **The pendant hypothesis at a regrowth wall, from the contraction forest alone**
(`W3ShiftStarExhaustionProof.pendant_at_wall'` without a nondegenerate request). -/
theorem pendant_at_wall_forest (w : Regrowth core y degree)
    (hForest : ContractionForest w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2
      (w.frame.edgeOf w.column))
    (hNoGlue : DanglingEdgeNoGlue w.limit)
    {e : (w.frame.limitTarget w.column).edges}
    (hInc : (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 =
        mergeVertex w ∨
      (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 =
        mergeVertex w) (b : Fin degree) (D : Fin degree → Prop)
    (hDsub : ∀ s, D s → (w.limit.vertexPartition (mergeVertex w)).Rel b s)
    (hDang : ∀ s, D s → IsDangling w.limit (w.limit.sourceEdge e s))
    (hPos : 0 < nonDanglingValency w.limit (w.limit.sourceEndpoint (mergeVertex w) b)) :
    Pendant w.limit (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) D := by
  have hVD : ∀ v, vertexMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) v = true →
      ∀ s, D s → nonDanglingValency w.limit (w.limit.sourceEndpoint v s) = 0 := by
    intro v hv s hs
    obtain ⟨cut⟩ := exists_branch_cut w.limit hInc (hDsub s hs) hPos (hDang s hs)
    exact nonDanglingValency_eq_zero_of_mem_side w.limit cut
      (mem_side_of_moved w.limit (farEnd_ne hInc) s cut rfl hv)
  have hED : ∀ f, edgeMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) f = true →
      ∀ s, D s → IsDangling w.limit (w.limit.sourceEdge f s) := by
    intro f hf s hs
    have hEnd : ∃ u, vertexMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) u =
        true ∧ f ∈ GluingDatum.incidentEdges u := by
      unfold edgeMoved at hf
      rcases Bool.or_eq_true_iff.mp hf with h | h
      · exact ⟨_, h, by simp [GluingDatum.incidentEdges]⟩
      · exact ⟨_, h, by simp [GluingDatum.incidentEdges]⟩
    obtain ⟨u, hu, hMem⟩ := hEnd
    exact (nonDanglingValency_eq_zero_iff w.limit _).mp (hVD u hu s hs) _
      (incident_sourceEdge_sourceEndpoint w.limit u f hMem s)
  refine ⟨?_, ?_, hVD, hED⟩
  · intro v hv s hs t hst
    have hvWall : v ≠ mergeVertex w := by
      intro h
      rw [h, vertexMoved_wall] at hv
      exact Bool.false_ne_true hv
    have hva : v.1 ≠ (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1 := by
      intro h
      exact hvWall (Subtype.ext h)
    have hvb : v.1 ≠ (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2 := v.2
    have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
      hForest
    set x := w.frame.data.sourceEndpoint v.1 s
    have hMap := WallDegeneration.nonDanglingValency_sourceVertexMap w.frame.data hCompat x hva hvb
    have hPart : w.limit.vertexPartition v = w.frame.data.vertexPartition v.1 :=
      contractVertexPartition_of_ne w.frame.data _ _ hva
    have hImage : sourceVertexMap w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) x = w.limit.sourceEndpoint v s := by
      change w.limit.sourceEndpoint (GraphContraction.fold _ _ v.1)
        ((w.frame.data.vertexPartition v.1).repr s) = _
      have hFold : GraphContraction.fold w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
          v.1 = v := GraphContraction.fold_coe _ _ v
      refine (congrArg (fun z : (w.frame.limitTarget w.column).V ↦
        w.limit.sourceEndpoint z ((w.frame.data.vertexPartition v.1).repr s)) hFold).trans ?_
      apply M11StarExhaustionProof.sourceEndpoint_of_rel
      rw [hPart]
      exact (w.frame.data.vertexPartition v.1).rel_repr_left s
    rw [hImage] at hMap
    have h0 : nonDanglingValency w.frame.data x = 0 := hMap.symm.trans (hVD v hv s hs)
    obtain ⟨hOne, -⟩ := PendantFibre.degree_one_of_nonDanglingValency_zero w.frame.fullDim x h0
    change (w.frame.data.vertexPartition v.1).blockCard
      ((w.frame.data.vertexPartition v.1).repr s) = 1 at hOne
    have hBlock := (w.frame.data.vertexPartition v.1).block_eq_of_rel
      ((w.frame.data.vertexPartition v.1).rel_repr_right s)
    unfold SheetPartition.blockCard at hOne
    rw [← hBlock] at hOne
    have hSingle := (w.frame.data.vertexPartition v.1).block_eq_singleton_of_blockCard_eq_one
      s hOne
    rw [hPart] at hst
    have hMem := ((w.frame.data.vertexPartition v.1).mem_block_iff s t).mpr hst
    rw [hSingle, Finset.mem_singleton] at hMem
    exact hMem
  · intro f hf s hs t hst
    have hIndex := hNoGlue _ (hED f hf s hs)
    change (w.limit.edgePartition f).blockCard ((w.limit.edgePartition f).repr s) = 1 at hIndex
    have hBlock := (w.limit.edgePartition f).block_eq_of_rel
      ((w.limit.edgePartition f).rel_repr_right s)
    unfold SheetPartition.blockCard at hIndex
    rw [← hBlock] at hIndex
    have hSingle := (w.limit.edgePartition f).block_eq_singleton_of_blockCard_eq_one s hIndex
    have hMem := ((w.limit.edgePartition f).mem_block_iff s t).mpr hst
    rw [hSingle, Finset.mem_singleton] at hMem
    exact hMem

/-- **Moving a set of dangling sheets onto another, on one branch.**  A limit isomorphism into a
regrowth's limit is followed by a pendant automorphism on the branch of the incident
occurrence `X`, which leaves the target maps, the wall permutation and every other incident
occurrence's permutation alone, and carries a prescribed set `P` of the anchor class's sheets
dangling above `X` onto another such set `Q` of the same size. -/
theorem exists_realign_set {T₁ : CFGraph} {first : GluingDatum T₁ degree}
    (w : Regrowth core y degree)
    (hForest : ContractionForest w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2
      (w.frame.edgeOf w.column))
    (hNoGlue : DanglingEdgeNoGlue w.limit)
    (ψ : GeometricDatumIso first w.limit) (X : (w.frame.limitTarget w.column).edges)
    (hX : X ∈ GluingDatum.incidentEdges (mergeVertex w)) (A : Fin degree)
    (hPos : 0 < nonDanglingValency w.limit (w.limit.sourceEndpoint (mergeVertex w) A))
    (P Q : Finset (Fin degree))
    (hP : ∀ y ∈ P, (w.limit.vertexPartition (mergeVertex w)).Rel A y ∧
      IsDangling w.limit (w.limit.sourceEdge X y))
    (hQ : ∀ y ∈ Q, (w.limit.vertexPartition (mergeVertex w)).Rel A y ∧
      IsDangling w.limit (w.limit.sourceEdge X y))
    (hcard : P.card = Q.card) :
    ∃ ψ' : GeometricDatumIso first w.limit,
      (∀ e, ψ'.targetEdge e = ψ.targetEdge e) ∧ (∀ v, ψ'.targetVertex v = ψ.targetVertex v) ∧
      (∀ v, ψ.targetVertex v = mergeVertex w → ψ'.vertexPerm v = ψ.vertexPerm v) ∧
      (∀ e, ψ.targetEdge e ∈ GluingDatum.incidentEdges (mergeVertex w) → ψ.targetEdge e ≠ X →
        ψ'.edgePerm e = ψ.edgePerm e) ∧
      (∀ e, ψ.targetEdge e = X → ∀ s, (ψ'.edgePerm e s ∈ Q ↔ ψ.edgePerm e s ∈ P)) := by
  classical
  have hIncX := ends_of_mem hX
  set D : Fin degree → Prop := fun s ↦
    (w.limit.vertexPartition (mergeVertex w)).Rel A s ∧
      IsDangling w.limit (w.limit.sourceEdge X s)
  have hPend := pendant_at_wall_forest w hForest hNoGlue hIncX A D (fun s hs ↦ hs.1)
    (fun s hs ↦ hs.2) hPos
  obtain ⟨π, hπ, hπD, hπQ⟩ := exists_perm_image D P Q hP hQ hcard
  have hD : ∀ s t, D s → D t → (w.limit.vertexPartition (mergeVertex w)).Rel s t :=
    fun s t hs ht ↦ hs.1.symm.trans ht.1
  set θ := pendantIso hPend hD π hπ hπD
  refine ⟨ψ.trans θ, fun _ ↦ rfl, fun _ ↦ rfl, fun v hv ↦ ?_, fun e he hne ↦ ?_, fun e he s ↦ ?_⟩
  · refine Equiv.ext fun s ↦ ?_
    change branchPerm (vertexMoved (mergeVertex w) (farEnd (mergeVertex w) X) (farEnd_ne hIncX)
      (ψ.targetVertex v)) π (ψ.vertexPerm v s) = ψ.vertexPerm v s
    rw [hv, vertexMoved_wall]
    rfl
  · refine Equiv.ext fun s ↦ ?_
    change branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) X) (farEnd_ne hIncX)
      (ψ.targetEdge e)) π (ψ.edgePerm e s) = ψ.edgePerm e s
    rw [edgeMoved_other (W4StarParity.limitTarget_connected w) (W4StarParity.limitTarget_genus w)
      hIncX (ends_of_mem he) hne]
    rfl
  · change branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) X) (farEnd_ne hIncX)
      (ψ.targetEdge e)) π (ψ.edgePerm e s) ∈ Q ↔ _
    rw [he, edgeMoved_self hIncX]
    exact hπQ _

end PendantRealign

/-! ## 6.  The placement, and the incoming resolution read in limit coordinates -/

section Placement

open ValencyThreeSplit
open W3Nd2SourceCandidates (rightOf)
open W3Nd2IncomingTargetPlacement (divalentOccurrence divalentOccurrence_unique
  divalentOccurrence_placement)

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (H : AnchorInput data hc hab hOne block)
  (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

omit [Fintype coordinate] [DecidableEq coordinate] in
include hc in
theorem unfold_mem_ends {e : (contract target hab hOne).edges}
    (he : e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩) :
    unfoldEdge hc hab hOne e ∈ GluingDatum.incidentEdges a ∨
      unfoldEdge hc hab hOne e ∈ GluingDatum.incidentEdges b := by
  have hf := fold_unfoldEdge hc hab hOne e
  rcases (mem_incidentEdges_iff _ e).mp he with h | h
  · have h1 : fold target hab (unfoldEdge hc hab hOne e : target.V × target.V).1 = ⟨a, hab⟩ :=
      (congrArg Prod.fst hf).trans h
    rcases (GraphContraction.fold_eq_iff target hab _ _).mp h1 with h2 | ⟨-, h2⟩
    · exact Or.inl ((mem_incidentEdges_iff a _).mpr (Or.inl h2))
    · exact Or.inr ((mem_incidentEdges_iff b _).mpr (Or.inl h2))
  · have h1 : fold target hab (unfoldEdge hc hab hOne e : target.V × target.V).2 = ⟨a, hab⟩ :=
      (congrArg Prod.snd hf).trans h
    rcases (GraphContraction.fold_eq_iff target hab _ _).mp h1 with h2 | ⟨-, h2⟩
    · exact Or.inl ((mem_incidentEdges_iff a _).mpr (Or.inr h2))
    · exact Or.inr ((mem_incidentEdges_iff b _).mpr (Or.inr h2))

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem label_edgePartition (i : Fin 4) :
    (contractDatum data hc hab hOne).edgePartition (L.e i).1.1 =
      data.edgePartition (lift L i).1.1 := by
  rw [← sourceEdgeMap_lift L i]
  exact contractDatum_edgePartition_foldEdge data hc hab hOne ⟨_, lift_ne L i⟩

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem label_sheet (i : Fin 4) : (L.e i).1.2 = (lift L i).1.2 := by
  rw [← sourceEdgeMap_lift L i]
  rfl

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem label_unfold (i : Fin 4) : unfoldEdge hc hab hOne (L.e i).1.1 = (lift L i).1.1 := by
  rw [← sourceEdgeMap_lift L i]
  exact unfoldEdge_foldEdge hc hab hOne ⟨_, lift_ne L i⟩

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem label_mem (i : Fin 4) :
    (L.e i).1.1 ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
  target_mem_incidentEdges _ ((mem_ndAt _ _ _).mp (L.mem i)).2

include fd H in
/-- **The placement isolating the divalent side's direction**, and the incoming resolution at
it: the retained endpoint is the divalent one, the fresh endpoint the trivalent one. -/
theorem placement_facts (i₀ : Fin 4)
    (hTu : (lift L i₀).1.1 ∈ GluingDatum.incidentEdges (divEnd a b)) :
    ∃ hP : (∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne e = rightOf (L.e i₀).1.1 e) ∨
      (∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne e = !(rightOf (L.e i₀).1.1 e)),
      (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).left =
          data.vertexPartition (divEnd a b) ∧
        (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).right =
          data.vertexPartition (triEnd a b) ∧
        (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).newEdge =
          data.edgePartition contracted := by
  classical
  obtain ⟨huv, hu2, hv3, -, -⟩ := H.sides fd
  set U := (L.e i₀).1.1
  set T := (lift L i₀).1.1
  have hUT : unfoldEdge hc hab hOne U = T := label_unfold L i₀
  have hU : U ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
    label_mem L i₀
  have hTne : T ≠ contracted := lift_ne L i₀
  have hnab : ¬ (((T : target.V × target.V).1 = a ∨ (T : target.V × target.V).2 = a) ∧
      ((T : target.V × target.V).1 = b ∨ (T : target.V × target.V).2 = b)) := by
    rintro ⟨ha', hb'⟩
    apply hTne
    apply M11BranchSeparation.target_occurrence_unique hOne T contracted _ (Or.inl hc)
    rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2
    · exact (hab (h1.symm.trans h2)).elim
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h2 h1)
    · exact (hab (h1.symm.trans h2)).elim
  have hright : IncomingTargetExpansion.right hc hab hOne U =
      decide ((T : target.V × target.V).1 = b ∨ (T : target.V × target.V).2 = b) := by
    unfold IncomingTargetExpansion.right
    rw [hUT]
  have hTu' := (mem_incidentEdges_iff _ _).mp hTu
  have hcase : ((GluingDatum.incidentEdges a).card = 2 ∧
        IncomingTargetExpansion.right hc hab hOne U = false) ∨
      ((GluingDatum.incidentEdges b).card = 2 ∧
        IncomingTargetExpansion.right hc hab hOne U = true) := by
    rcases huv with ⟨hua, -⟩ | ⟨hub, -⟩
    · rw [hua] at hu2 hTu'
      refine Or.inl ⟨hu2, ?_⟩
      rw [hright]
      exact decide_eq_false fun h ↦ hnab ⟨hTu', h⟩
    · rw [hub] at hu2 hTu'
      refine Or.inr ⟨hu2, ?_⟩
      rw [hright]
      exact decide_eq_true hTu'
  have hdU : divalentOccurrence data hc hab hOne fd H.star = U :=
    (divalentOccurrence_unique data hc hab hOne fd H.star U ⟨hU, hcase⟩).symm
  have hP0 := divalentOccurrence_placement data hc hab hOne fd H.star
  rw [hdU] at hP0
  refine ⟨hP0, ?_⟩
  have hpair := M11IncomingOuterPartitions.transported_endpointPartitions data hc hab hOne
    (rightOf U) hP0
  have hnew := M11IncomingOuterPartitions.transported_edgePartition_new data hc hab hOne
    (rightOf U) hP0 fd.targetConnected fd.targetGenus
  have hUU : rightOf U U = false := by simp [rightOf]
  by_cases hsup : ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne e = rightOf U e
  · rw [ite_eq_left hsup] at hpair
    have hRU := (hsup U hU).trans hUU
    have huv' : divEnd a b = a ∧ triEnd a b = b := by
      rcases huv with h | ⟨hub, hva⟩
      · exact h
      · exfalso
        rcases hcase with ⟨h2, -⟩ | ⟨-, h2⟩
        · rw [hub] at hu2; rw [hva] at hv3; omega
        · rw [hRU] at h2; exact Bool.false_ne_true h2
    rw [huv'.1, huv'.2]
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair, hnew⟩
  · rw [ite_eq_right hsup] at hpair
    have hRU : IncomingTargetExpansion.right hc hab hOne U = true := by
      rcases hP0 with h | h
      · exact (hsup h).elim
      · rw [h U hU, hUU]; rfl
    have huv' : divEnd a b = b ∧ triEnd a b = a := by
      rcases huv with ⟨hua, hvb⟩ | h
      · exfalso
        rcases hcase with ⟨-, h2⟩ | ⟨h2, -⟩
        · rw [hRU] at h2; exact Bool.false_ne_true h2.symm
        · rw [hvb] at hv3; omega
      · exact h
    rw [huv'.1, huv'.2]
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair, hnew⟩

end Placement

/-! ## 7.  The incoming resolution of a cover, read off its split -/

section Cover

open ValencyThreeSplit
open W3Nd2SourceCandidates (rightOf)
open ValencyThreeGeneral.Split7

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (H : AnchorInput data hc hab hOne block)
  (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

include fd H in
/-- **A cover reading `base₂`**: its incoming resolution, at the placement isolating `e₂`'s
direction, is `e₂ ∪ e₅` merged on the divalent side and the new edge, and the whole merged
partition on the trivalent side. -/
theorem cover_two (hs : Reads L (divEnd a b) .base₂) :
    ∃ hP : (∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne e = rightOf (L.e 0).1.1 e) ∨
      (∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne e = !(rightOf (L.e 0).1.1 e)),
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).left.Rel s t ↔
        MergeRel ((contractDatum data hc hab hOne).edgePartition (L.e 0).1.1) (L.e 0).1.2
          (L.e 3).1.2 s t) ∧
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).newEdge.Rel s t ↔
        (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).left.Rel s t) ∧
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).right.Rel s t ↔
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel s t) ∧
      (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).left.Refines
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩) := by
  classical
  obtain ⟨huv, hu2, hv3, hchu, hchv⟩ := H.sides fd
  obtain ⟨-, -, hne_uv⟩ := side_of_huv hab huv
  rcases shape data fd hc hab hOne block (divEnd a b) (triEnd a b) H.forest H.compat H.nd4 huv
      hu2 hchu hchv with ⟨⟨P⟩⟩ | ⟨⟨P⟩⟩
  · obtain ⟨X, hX, hXu, h0, h3⟩ := hs
    have hXR : X = P.R := by
      have hX' := hX
      rw [P.fib_eq] at hX'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX'
      rcases hX' with h | h
      · exact h
      · exact (hne_uv (hXu.symm.trans (h ▸ P.Y_over))).elim
    rw [hXR] at h0 h3
    have h0' : lift L 0 ∈ bdAt data contracted P.R := (mem_bdAt data _ _).mpr ⟨h0, lift_ne L 0⟩
    have h3' : lift L 3 ∈ bdAt data contracted P.R := (mem_bdAt data _ _).mpr ⟨h3, lift_ne L 3⟩
    have hne : lift L 0 ≠ lift L 3 := fun h ↦ absurd (lift_injective L h) (by decide)
    obtain ⟨hPu, hPt, hPv⟩ := two_shape data fd hc hab H.forest huv hu2 hchu P h0' h3' hne
    have hTu : (lift L 0).1.1 ∈ GluingDatum.incidentEdges (divEnd a b) := by
      have h := target_mem_incidentEdges data ((mem_ndAt data _ _).mp h0).2
      rwa [P.R_over] at h
    obtain ⟨hP, hl, hr, hn⟩ := placement_facts fd H L 0 hTu
    refine ⟨hP, ?_, ?_, ?_, ?_⟩
    · intro s t
      rw [hl, label_edgePartition L 0, label_sheet L 0, label_sheet L 3]
      exact hPu s t
    · intro s t
      rw [hn, hl]
      exact hPt s t
    · intro s t
      rw [hr, contractDatum_vertexPartition_merge]
      exact hPv s t
    · rw [hl, contractDatum_vertexPartition_merge]
      exact refines_merged_u data huv
  · exfalso
    obtain ⟨α4, δ5, hr, -⟩ := reads_three fd L P H.compat (H.noGlue fd) (H.ram_one fd) H.nd4
      huv hv3
    have := P.reads_eq fd L H.compat H.nd4 huv hv3 hs hr
    cases this

include fd H in
/-- **A cover reading `simple α δ`**: its incoming resolution, at the placement isolating
`e_α`'s direction, is `e_α`'s partition on the divalent side, the merged partition with the
class `A'` of `e_δ` split off the anchor on the trivalent side, and their common refinement
on the new edge; `A'` lies in `e_α`'s class and dangles above the third direction. -/
theorem cover_three (α4 δ5 : Bool) (hs : Reads L (divEnd a b) (.simple α4 δ5)) :
    ∃ hP : (∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne e = rightOf (L.e (alphaIdx α4)).1.1 e) ∨
      (∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne e = !(rightOf (L.e (alphaIdx α4)).1.1 e)),
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).left.Rel s t ↔
        ((contractDatum data hc hab hOne).edgePartition (L.e (alphaIdx α4)).1.1).Rel s t) ∧
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).right.Rel s t ↔
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel s t ∧
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 s →
          (((contractDatum data hc hab hOne).edgePartition (L.e (deltaIdx δ5)).1.1).Rel
              (L.e (deltaIdx δ5)).1.2 s ↔
            ((contractDatum data hc hab hOne).edgePartition (L.e (deltaIdx δ5)).1.1).Rel
              (L.e (deltaIdx δ5)).1.2 t))) ∧
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).newEdge.Rel s t ↔
        (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).left.Rel s t ∧
          (M11WallExhaustion.incomingResolution data hc hab hOne _ hP).right.Rel s t) ∧
      (∀ s, ((contractDatum data hc hab hOne).edgePartition (L.e (deltaIdx δ5)).1.1).Rel
          (L.e (deltaIdx δ5)).1.2 s →
        ((contractDatum data hc hab hOne).edgePartition (L.e (alphaIdx α4)).1.1).Rel
          (L.e (alphaIdx α4)).1.2 s) ∧
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1
        (L.e (deltaIdx δ5)).1.2 ∧
      (∀ s, ((contractDatum data hc hab hOne).edgePartition (L.e (deltaIdx δ5)).1.1).Rel
          (L.e (deltaIdx δ5)).1.2 s →
        ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
          e ≠ (L.e (alphaIdx α4)).1.1 → e ≠ (L.e (deltaIdx δ5)).1.1 →
            IsDangling (contractDatum data hc hab hOne)
              ((contractDatum data hc hab hOne).sourceEdge e s)) := by
  classical
  obtain ⟨huv, hu2, hv3, hchu, hchv⟩ := H.sides fd
  obtain ⟨-, -, hne_uv⟩ := side_of_huv hab huv
  rcases shape data fd hc hab hOne block (divEnd a b) (triEnd a b) H.forest H.compat H.nd4 huv
      hu2 hchu hchv with ⟨⟨P⟩⟩ | ⟨⟨P⟩⟩
  · exfalso
    have := P.reads_eq L hs
    cases this
  obtain ⟨⟨X, hX, hXu, hα⟩, ⟨Z', hZ', hZ2, hδ⟩⟩ := hs
  have hXR : X = P.R := by
    have hX' := hX
    rw [P.fib_eq] at hX'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX'
    rcases hX' with h | h | h
    · exact h
    · exact (hne_uv (hXu.symm.trans (h ▸ P.Y_over))).elim
    · exact (hne_uv (hXu.symm.trans (h ▸ P.Z_over))).elim
  have hZZ : Z' = P.Z := by
    have hZ'' := hZ'
    rw [P.fib_eq] at hZ''
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ''
    rcases hZ'' with h | h | h
    · rw [h, P.R_nd] at hZ2; exact absurd hZ2 (by norm_num)
    · rw [h, P.Y_nd] at hZ2; exact absurd hZ2 (by norm_num)
    · exact h
  rw [hXR] at hα
  rw [hZZ] at hδ
  have hα' : lift L (alphaIdx α4) ∈ bdAt data contracted P.R :=
    (mem_bdAt data _ _).mpr ⟨hα, lift_ne L _⟩
  have hδ' : lift L (deltaIdx δ5) ∈ bdAt data contracted P.Z :=
    (mem_bdAt data _ _).mpr ⟨hδ, lift_ne L _⟩
  obtain ⟨hPu, hPv, hPt, hZR, hZA, hDang⟩ :=
    three_shape data fd hc hab H.forest huv hu2 hchu P hα' hδ'
  have hTu : (lift L (alphaIdx α4)).1.1 ∈ GluingDatum.incidentEdges (divEnd a b) := by
    have h := target_mem_incidentEdges data ((mem_ndAt data _ _).mp hα).2
    rwa [P.R_over] at h
  obtain ⟨hP, hl, hr, hn⟩ := placement_facts fd H L (alphaIdx α4) hTu
  have hEα := label_edgePartition L (alphaIdx α4)
  have hEδ := label_edgePartition L (deltaIdx δ5)
  have hmα := label_sheet L (alphaIdx α4)
  have hmδ := label_sheet L (deltaIdx δ5)
  have hW := contractDatum_vertexPartition_merge data hc hab hOne
  refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t; rw [hl, hEα]; exact hPu s t
  · intro s t; rw [hr, hW, hEδ, hmδ]; exact hPv s t
  · intro s t; rw [hn, hl, hr]; exact hPt s t
  · intro s; rw [hEδ, hEα, hmδ, hmα]; exact hZR s
  · rw [hW, hmδ]; exact hZA
  · intro s hs e he heU heΔ
    rw [hEδ, hmδ] at hs
    have hTuα := hTu
    have hne_c : unfoldEdge hc hab hOne e ≠ contracted := unfoldEdge_ne_contracted hc hab hOne e
    have hinj : ∀ i : Fin 4, unfoldEdge hc hab hOne e = (lift L i).1.1 → e = (L.e i).1.1 := by
      intro i h
      rw [← label_unfold L i] at h
      rw [← foldEdge_unfoldEdge hc hab hOne e hne_c,
        ← foldEdge_unfoldEdge hc hab hOne (L.e i).1.1 (unfoldEdge_ne_contracted hc hab hOne _)]
      congr 2
    have hv : unfoldEdge hc hab hOne e ∈ GluingDatum.incidentEdges (triEnd a b) := by
      have hu_or : unfoldEdge hc hab hOne e ∉ GluingDatum.incidentEdges (divEnd a b) := by
        intro hmem
        obtain ⟨x, y, hxy, hEq⟩ := Finset.card_eq_two.mp hu2
        have hcu := contracted_mem_incidentEdges hc (side_of_huv hab huv).1
        have hTne := lift_ne L (alphaIdx α4)
        rw [hEq] at hmem hcu hTuα
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hcu hTuα
        apply heU
        apply hinj (alphaIdx α4)
        rcases hmem with h1 | h1 <;> rcases hcu with h2 | h2 <;> rcases hTuα with h3 | h3
        all_goals first
          | exact (hne_c (h1.trans h2.symm)).elim
          | exact (hTne (h3.trans h2.symm)).elim
          | exact h1.trans h3.symm
      rcases unfold_mem_ends (hc := hc) he with h | h <;>
        rcases huv with ⟨hua, hvb⟩ | ⟨hub, hva⟩
      · exact (hu_or (by rw [hua]; exact h)).elim
      · rw [hva]; exact h
      · rw [hvb]; exact h
      · exact (hu_or (by rw [hub]; exact h)).elim
    have hneδ : unfoldEdge hc hab hOne e ≠ (lift L (deltaIdx δ5)).1.1 :=
      fun h ↦ heΔ (hinj _ h)
    have hd := hDang s hs _ hv hne_c hneδ
    have hmap := H.compat.1 ⟨data.sourceEdge (unfoldEdge hc hab hOne e) s, hne_c⟩ hd
    convert hmap using 1
    apply Subtype.ext
    apply Prod.ext
    · exact (foldEdge_unfoldEdge hc hab hOne e hne_c).symm
    · rfl

end Cover

/-! ## 8.  `ResolutionMatch`, with no hypothesis -/

section Assembly

open ValencyThreeSplit ValencyThreeRigidity
open DraismaVargas.Count.WallStar (Regrowth)
open Utilities.Certificate.ExplicitPotential (Core)
open W3Nd2SourceCandidates (rightOf)
open W3Nd2StarExhaustionProof (edge_rel_iff edgePerm_agree incident_iff)
open ValencyThreeGeneral.Split7

variable {n p : ℕ}

/-- **Stage 4, `ResolutionMatch`, in general.**  At any core, request and
degree: two regrowths at valency-three anchors, a labelled-metric isomorphism `ψ` of their
limits, labellings transported along `ψ` and the same read split admit placements and a
labelled-metric isomorphism `ψ'` (equal to `ψ` for base tree `T₂`; `ψ` followed by a pendant
automorphism on the third direction's branch for base tree `T_α`) carrying a decoupled
transport of the two incoming resolutions.  The oddness hypotheses are not used. -/
theorem resolutionMatch (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    ResolutionMatch core y degree := by
  classical
  intro w w' block block' H H' ψ hψ L L' hL _ _ s hs hs'
  have hlim := sourceVertexEquiv_limA w w' H H' ψ
  have hWall : ψ.targetVertex ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩ =
      ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩ :=
    congrArg (fun x : w'.limit.SourceVertex ↦ x.1.1) hlim
  have hA : (w'.limit.vertexPartition ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩).Rel
      block'.1 (ψ.vertexPerm ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩ block.1) := by
    have h2 : ψ.vertexPerm ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩ block.1 = block'.1 :=
      congrArg (fun x : w'.limit.SourceVertex ↦ x.1.2) hlim
    change (w'.limit.vertexPartition _).repr block'.1 =
      (w'.limit.vertexPartition _).repr (ψ.vertexPerm _ block.1)
    rw [h2]
  have hLe : ∀ i, (L'.e i).1.1 = ψ.targetEdge (L.e i).1.1 :=
    fun i ↦ congrArg (fun x : w'.limit.SourceEdge ↦ x.1.1) (hL i)
  have hLm : ∀ i, (L'.e i).1.2 = ψ.edgePerm (L.e i).1.1 (L.e i).1.2 :=
    fun i ↦ congrArg (fun x : w'.limit.SourceEdge ↦ x.1.2) (hL i)
  rcases s with _ | ⟨α4, δ5⟩
  · -- base tree `T₂`: no coherence is needed
    obtain ⟨hP, hl, hn, hr, href⟩ := cover_two w.frame.fullDim H L hs
    obtain ⟨hP', hl', hn', hr', -⟩ := cover_two w'.frame.fullDim H' L' hs'
    refine ⟨rightOf (L.e 0).1.1, hP, rightOf (L'.e 0).1.1, hP', ψ, hψ, ?_⟩
    refine transportFree_two ψ hWall (L.e 0).1.1 (label_mem L 0) (L'.e 0).1.1 (hLe 0).symm
      _ _ (L.e 0).1.2 (L.e 3).1.2 (L'.e 0).1.2 (L'.e 3).1.2 hl hl' hn hn' hr hr' href ?_ ?_
    · rw [hLm 0]; exact rfl
    · rw [hLm 3, ← L.dir25]; exact rfl
  · -- base tree `T_α`: realign `A'` on the third direction's branch
    obtain ⟨hP, hl, hr, hn, hZR, hZA, hDang⟩ := cover_three w.frame.fullDim H L α4 δ5 hs
    obtain ⟨hP', hl', hr', hn', hZR', hZA', hDang'⟩ := cover_three w'.frame.fullDim H' L' α4 δ5 hs'
    set wall : (w.frame.limitTarget w.column).V := ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩
    set wall' : (w'.frame.limitTarget w'.column).V :=
      ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩
    set U := (L.e (alphaIdx α4)).1.1
    set Δ := (L.e (deltaIdx δ5)).1.1
    set mα := (L.e (alphaIdx α4)).1.2
    set mδ := (L.e (deltaIdx δ5)).1.2
    have hUΔ : U ≠ Δ := by
      have d25 := L.dir25
      have d3 := L.dir3
      have d4 := L.dir4
      have hα : alphaIdx α4 = 1 ∨ alphaIdx α4 = 2 := by cases α4 <;> simp [alphaIdx]
      have hδ : deltaIdx δ5 = 0 ∨ deltaIdx δ5 = 3 := by cases δ5 <;> simp [deltaIdx]
      show (L.e (alphaIdx α4)).1.1 ≠ (L.e (deltaIdx δ5)).1.1
      rcases hα with h | h <;> rcases hδ with h' | h' <;> rw [h, h']
      · exact d3
      · rw [← d25]; exact d3
      · exact d4
      · rw [← d25]; exact d4
    have memU : U ∈ GluingDatum.incidentEdges wall := label_mem L _
    have memΔ : Δ ∈ GluingDatum.incidentEdges wall := label_mem L _
    have hcard3 : (GluingDatum.incidentEdges wall).card = 3 := H.valency
    have hrest : (((GluingDatum.incidentEdges wall).erase U).erase Δ).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hUΔ.symm, memΔ⟩),
        Finset.card_erase_of_mem memU, hcard3]
    obtain ⟨X, hXset⟩ := Finset.card_eq_one.mp hrest
    have hXmem : X ∈ ((GluingDatum.incidentEdges wall).erase U).erase Δ := by
      rw [hXset]; exact Finset.mem_singleton_self X
    obtain ⟨hXΔ, hX1⟩ := Finset.mem_erase.mp hXmem
    obtain ⟨hXU, memX⟩ := Finset.mem_erase.mp hX1
    have hEdges : ∀ e, e ∈ GluingDatum.incidentEdges wall ↔ e = U ∨ e = Δ ∨ e = X := by
      intro e
      constructor
      · intro he
        by_cases h1 : e = U
        · exact Or.inl h1
        by_cases h2 : e = Δ
        · exact Or.inr (Or.inl h2)
        have : e ∈ ((GluingDatum.incidentEdges wall).erase U).erase Δ :=
          Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, he⟩⟩
        rw [hXset] at this
        exact Or.inr (Or.inr (Finset.mem_singleton.mp this))
      · rintro (rfl | rfl | rfl)
        · exact memU
        · exact memΔ
        · exact memX
    -- the images on the second side
    have hU' : (L'.e (alphaIdx α4)).1.1 = ψ.targetEdge U := hLe _
    have hΔ' : (L'.e (deltaIdx δ5)).1.1 = ψ.targetEdge Δ := hLe _
    have hmα' : (L'.e (alphaIdx α4)).1.2 = ψ.edgePerm U mα := hLm _
    have hmδ' : (L'.e (deltaIdx δ5)).1.2 = ψ.edgePerm Δ mδ := hLm _
    have hX' : ψ.targetEdge X ∈ GluingDatum.incidentEdges wall' :=
      (incident_iff ψ hWall X).mp (ends_of_mem memX)
    have hXU' : ψ.targetEdge X ≠ (L'.e (alphaIdx α4)).1.1 := by
      rw [hU']; exact fun h ↦ hXU (ψ.targetEdge.injective h)
    have hXΔ' : ψ.targetEdge X ≠ (L'.e (deltaIdx δ5)).1.1 := by
      rw [hΔ']; exact fun h ↦ hXΔ (ψ.targetEdge.injective h)
    -- the two copies of `A'`, and the realignment
    set Z := Finset.univ.filter fun x ↦ (w.limit.edgePartition Δ).Rel mδ x
    set P := Z.image (ψ.edgePerm X)
    set Q := Finset.univ.filter fun x ↦
      (w'.limit.edgePartition (L'.e (deltaIdx δ5)).1.1).Rel (L'.e (deltaIdx δ5)).1.2 x
    have hZmap : ∀ x, (w.limit.edgePartition Δ).Rel mδ x ↔
        (w'.limit.edgePartition (L'.e (deltaIdx δ5)).1.1).Rel (L'.e (deltaIdx δ5)).1.2
          (ψ.edgePerm Δ x) := by
      intro x
      rw [edge_rel_iff ψ Δ, hΔ', hmδ']
    have hQ : Q = Z.image (ψ.edgePerm Δ) := by
      ext q
      simp only [Q, Z, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        exact ⟨(ψ.edgePerm Δ).symm q, (hZmap _).mpr (by rw [Equiv.apply_symm_apply]; exact h),
          Equiv.apply_symm_apply _ _⟩
      · rintro ⟨x, hx, rfl⟩
        exact (hZmap x).mp hx
    have hcard : P.card = Q.card := by
      rw [hQ, Finset.card_image_of_injective _ (ψ.edgePerm X).injective,
        Finset.card_image_of_injective _ (ψ.edgePerm Δ).injective]
    have hZA_s : ∀ x ∈ Z, (w.limit.vertexPartition wall).Rel block.1 x := by
      intro x hx
      have hx' : (w.limit.edgePartition Δ).Rel mδ x := by simpa [Z] using hx
      exact hZA.trans ((StableLocalProperties.refines_of_mem_incidentEdges w.limit memΔ).rel hx')
    have hPD : ∀ q ∈ P, (w'.limit.vertexPartition wall').Rel block'.1 q ∧
        IsDangling w'.limit (w'.limit.sourceEdge (ψ.targetEdge X) q) := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      have hx' : (w.limit.edgePartition Δ).Rel mδ x := by simpa [Z] using hx
      refine ⟨(anchor_iff ψ hWall block.1 block'.1 hA (ψ.edgePerm X)
        (edgePerm_agree ψ hWall X hX') x).mp (hZA_s x hx), ?_⟩
      exact (W3ShiftStarExhaustionProof.isDangling_sourceEdge_iff ψ
        (connected_limit w) X x).mpr (hDang x hx' X memX hXU hXΔ)
    have hQD : ∀ q ∈ Q, (w'.limit.vertexPartition wall').Rel block'.1 q ∧
        IsDangling w'.limit (w'.limit.sourceEdge (ψ.targetEdge X) q) := by
      intro q hq
      have hq' : (w'.limit.edgePartition (L'.e (deltaIdx δ5)).1.1).Rel
          (L'.e (deltaIdx δ5)).1.2 q := by simpa [Q] using hq
      refine ⟨hZA'.trans ((StableLocalProperties.refines_of_mem_incidentEdges w'.limit
        (label_mem L' _)).rel hq'), hDang' q hq' _ hX' hXU' hXΔ'⟩
    have hPos : 0 < nonDanglingValency w'.limit (w'.limit.sourceEndpoint wall' block'.1) := by
      have hEq : w'.limit.sourceEndpoint wall' block'.1 = anchorOf w' block' :=
        Subtype.ext (Prod.ext rfl (anchorOf w' block').2)
      have h4 : nonDanglingValency w'.limit (anchorOf w' block') = 4 := H'.nd4
      rw [hEq, h4]
      norm_num
    obtain ⟨ψ', h₁, h₂, h₃, h₄, h₅⟩ := exists_realign_set w' H'.forest
      (H'.noGlue w'.frame.fullDim) ψ (ψ.targetEdge X) hX' block'.1 hPos P Q hPD hQD hcard
    refine ⟨rightOf U, hP, rightOf (L'.e (alphaIdx α4)).1.1, hP', ψ', fun e ↦ ?_, ?_⟩
    · rw [h₁ e]; exact hψ e
    have hWall' : ψ'.targetVertex wall = wall' := (h₂ wall).trans hWall
    have hUn : ψ.targetEdge U ≠ ψ.targetEdge X := fun h ↦ hXU (ψ.targetEdge.injective h).symm
    have hΔn : ψ.targetEdge Δ ≠ ψ.targetEdge X := fun h ↦ hXΔ (ψ.targetEdge.injective h).symm
    have hψU : ψ'.edgePerm U = ψ.edgePerm U :=
      h₄ U ((incident_iff ψ hWall U).mp (ends_of_mem memU)) hUn
    have hψΔ : ψ'.edgePerm Δ = ψ.edgePerm Δ :=
      h₄ Δ ((incident_iff ψ hWall Δ).mp (ends_of_mem memΔ)) hΔn
    refine transportFree_three ψ' hWall' U Δ X hEdges hUΔ hXU.symm
      (L'.e (alphaIdx α4)).1.1 (L'.e (deltaIdx δ5)).1.1 ((h₁ U).trans hU'.symm)
      ((h₁ Δ).trans hΔ'.symm) _ _ block.1 block'.1 mα mδ (L'.e (alphaIdx α4)).1.2
      (L'.e (deltaIdx δ5)).1.2 hl hr hn hZR hl' hr' hn' hZR' ?_ ?_ ?_ ?_
    · rw [h₃ wall hWall]; exact hA
    · rw [hψU, hmα']; exact rfl
    · rw [hψΔ, hmδ']; exact rfl
    · intro x _
      have h5 := h₅ X rfl x
      simp only [Q, P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at h5
      rw [h5]
      constructor
      · intro hx
        exact ⟨x, by simpa [Z] using hx, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        rw [← (ψ.edgePerm X).injective hzx]
        simpa [Z] using hz

end Assembly

/-! ## 9.  Consequences: stage 4, `SplitRigidity`, and `FacetParity` modulo stage 3 -/

section Consequences

open ValencyThreeSplit ValencyThreeRigidity
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.FacetMachine
open DraismaVargas.Count.FacetAdapterPilot (farCore)
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft)

variable {n p : ℕ}

/-- **Stage 4 (`AnchorExtension`) in general.** -/
theorem anchorExtension (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    AnchorExtension core y degree :=
  anchorExtension_of_resolutionMatch (resolutionMatch core y degree)

/-- **`SplitRigidity` at every facet request over a connected core with at least three
vertices.** -/
theorem splitRigidity {core : Core n p} {y : Fin p → ℚ} {degree : ℕ} (hconn : core.Connected)
    (hn : 3 ≤ n) {e₀ : Fin p} (hy : y e₀ = 0) : SplitRigidity core y degree :=
  splitRigidity_of_resolutionMatch hconn hn hy (resolutionMatch core y degree)

/-- **`FacetParity` at a Whitehead step from stage 3 alone** (and uniqueness at the
non-valency-three limits): `facetParity_of_typeMatch_resolutionMatch` with both
`ResolutionMatch` inputs discharged. -/
theorem facetParity_of_typeMatch {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ} {degree : ℕ}
    (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    (h3 : TypeMatch c.core y₀ degree) (h3' : TypeMatch (farCore m').core y₀ degree)
    (hrest : ∀ m : MetricFacetLimit c.core (farCore m').core y₀ degree, ¬ V3Limit m →
      ∀ x x' : FrameClass c.core degree,
        x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x')
    (hrest' : ∀ m : MetricFacetLimit (farCore m').core c.core y₀ degree, ¬ V3Limit m →
      ∀ x x' : FrameClass (farCore m').core degree,
        x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x') :
    FacetParity c.core (farCore m').core degree y₀ :=
  facetParity_of_typeMatch_resolutionMatch m' hd hG hDegree hn h3
    (resolutionMatch _ _ _) h3' (resolutionMatch _ _ _) hrest hrest'

end Consequences

end DraismaVargas.Count.ValencyThreeResolutionMatch
