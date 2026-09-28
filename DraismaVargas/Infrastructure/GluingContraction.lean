import DraismaVargas.Infrastructure.GraphContraction
import DraismaVargas.Infrastructure.SheetJoin

/-!
# Contracting a gluing datum along one target edge

This is the limit gluing datum of Draisma--Vargas Part I (`def-limit-gluing`,
in the subsection on limits).  A gluing datum over a target graph is
pushed forward along the contraction of one target edge occurrence: the two
endpoint partitions of the contracted occurrence are replaced by their join
above the merged vertex, and every surviving target occurrence keeps its own
sheet partition.

The two halves this builds on are
`DraismaVargas/Infrastructure/GraphContraction.lean` (the contraction of the
target graph) and `DraismaVargas/Infrastructure/SheetJoin.lean` (the general
join of two sheet partitions).

The contracted occurrence is presented as `contracted : target.edges` together
with `hc : (contracted : target.V × target.V) = (a, b)`; the looplessness of
the target then gives `hab : a ≠ b` (`ne_of_coe_eq_pair`), and
`hOne : num_edges target a b = 1` says the occurrence is the only one joining
its endpoints.  `contractDatumAt` packages the instantiation in which `a` and
`b` are read off the occurrence, so that `hc` is `rfl`.

Fixing the edge partitions of the contracted datum is the fiddly part: the
edge multiset of the contracted graph is the *image* of the surviving pairs
under `fold`, and that image map identifies the pairs `(a, v)` and `(b, v)`.
The surviving occurrences are therefore re-indexed explicitly
(`foldIndex`, listing the occurrences at `b` after those at `a`), which makes
the resulting occurrence map `foldEdge` injective; a count then shows it is
bijective (`foldEdge_bijective`), and its inverse `unfoldEdge` is what the
contracted edge partition is read through.  So each surviving target
occurrence really does keep its own partition
(`contractDatum_edgePartition_foldEdge`), parallel target edges included.

Main results:

* `contractDatum`, `contractDatumAt` — the contracted gluing datum;
* `vertexPartition_refines` — every old vertex partition refines the one above
  its image, by `SheetPartition.left_refines_join` / `right_refines_join` at
  the merge;
* `sourceVertexMap`, `sourceVertexMap_surjective`, `sourceEdgeMap`,
  `sourceEdgeMap_injective`, `sourceEnds_sourceEdgeMap` — the correspondence of
  quotient sources;
* `sourceVertexMap_sourceEnds_eq_of_contracted` — an occurrence above the
  contracted target occurrence has both endpoints in one contracted source
  vertex, which is exactly the join condition;
* `connected_contractDatum`, `connected_contractDatumAt` — the contracted
  quotient source is still connected;
* `riemannHurwitzAtTargetVertex_contractDatum_of_ne` — away from the merged
  vertex the local Riemann--Hurwitz condition is inherited verbatim.  The
  inequality *at* the merged vertex is genuine Draisma--Vargas mathematics
  (ramification is additive under contraction only when the contracted source
  fibre is a forest) and is not proved here.
-/
namespace DraismaVargas.Infrastructure

namespace GluingContraction

open GraphContraction

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-! ### Occurrences of a multiset

`Multiset.ToType` is a sigma type, so Mathlib supplies no decidable equality
instance for it; the occurrence is however determined by its underlying
element together with its index, which is exactly `Multiset.coeEmbedding`. -/

/-- Decidable equality on the occurrences of a multiset. -/
scoped instance instDecidableEqOccurrence {α : Type*} [DecidableEq α] (m : Multiset α) :
    DecidableEq (↥m) := fun x y =>
  decidable_of_iff _ ((Multiset.coeEmbedding m).apply_eq_iff_eq x y)

/-! ### Elementary multiset counting -/

/-- Two distinct elements cannot together occur more often than the whole
multiset is long. -/
theorem count_add_count_le_card {α : Type*} [DecidableEq α] (s : Multiset α) {x y : α}
    (hxy : x ≠ y) : Multiset.count x s + Multiset.count y s ≤ Multiset.card s := by
  have hle : Multiset.replicate (Multiset.count x s) x
      + Multiset.replicate (Multiset.count y s) y ≤ s := by
    rw [Multiset.le_iff_count]
    intro z
    rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
    by_cases hzx : x = z
    · subst hzx
      rw [if_pos rfl, if_neg (fun h => hxy h.symm)]
      omega
    · rw [if_neg hzx]
      by_cases hzy : y = z
      · subst hzy
        rw [if_pos rfl]
        omega
      · rw [if_neg hzy]
        omega
  have hcard := Multiset.card_le_card hle
  rwa [Multiset.card_add, Multiset.card_replicate, Multiset.card_replicate] at hcard

/-- An element satisfying the filter predicate occurs at most as often as the
filtered multiset is long. -/
theorem count_le_card_filter {α : Type*} [DecidableEq α] (s : Multiset α)
    (p : α → Prop) [DecidablePred p] {x : α} (hx : p x) :
    Multiset.count x s ≤ Multiset.card (s.filter p) := by
  rw [← Multiset.count_filter_of_pos (p := p) (s := s) hx]
  exact Multiset.count_le_card _ _

/-- Two distinct elements satisfying the filter predicate. -/
theorem two_counts_le_card_filter {α : Type*} [DecidableEq α] (s : Multiset α)
    (p : α → Prop) [DecidablePred p] {x y : α} (hxy : x ≠ y) (hx : p x) (hy : p y) :
    Multiset.count x s + Multiset.count y s ≤ Multiset.card (s.filter p) := by
  rw [← Multiset.count_filter_of_pos (p := p) (s := s) hx,
    ← Multiset.count_filter_of_pos (p := p) (s := s) hy]
  exact count_add_count_le_card _ hxy

/-! ### The contracted occurrence is the only one joining its endpoints -/

/-- The endpoints of a target occurrence are distinct: the target is
loopless. -/
theorem ne_of_coe_eq_pair (hc : (contracted : target.V × target.V) = (a, b)) : a ≠ b := by
  rintro rfl
  exact target.loopless a (by rw [← hc]; exact Multiset.coe_mem)

/-- Under `hOne` the occurrences joining the two endpoints form the singleton
`{(a, b)}`. -/
theorem filter_eq_singleton (hc : (contracted : target.V × target.V) = (a, b))
    (hOne : num_edges target a b = 1) :
    target.edges.filter (fun e => e = (a, b) ∨ e = (b, a)) = {(a, b)} := by
  have hOne' : Multiset.card
      (target.edges.filter (fun e => e = (a, b) ∨ e = (b, a))) = 1 := hOne
  have hmem : ((a, b) : target.V × target.V) ∈
      target.edges.filter (fun e => e = (a, b) ∨ e = (b, a)) :=
    Multiset.mem_filter.mpr ⟨by rw [← hc]; exact Multiset.coe_mem, Or.inl rfl⟩
  obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hOne'
  rw [hx] at hmem ⊢
  rw [Multiset.mem_singleton] at hmem
  rw [hmem]

/-- The contracted pair occurs exactly once. -/
theorem count_pair_eq_one (hc : (contracted : target.V × target.V) = (a, b))
    (hOne : num_edges target a b = 1) :
    Multiset.count ((a, b) : target.V × target.V) target.edges = 1 := by
  have h : Multiset.count ((a, b) : target.V × target.V)
      (target.edges.filter (fun e => e = (a, b) ∨ e = (b, a))) = 1 := by
    rw [filter_eq_singleton hc hOne]
    simp
  rwa [Multiset.count_filter_of_pos (p := fun e : target.V × target.V => e = (a, b) ∨ e = (b, a))
    (a := ((a, b) : target.V × target.V)) (s := target.edges) (Or.inl rfl)] at h

/-- The reversed pair does not occur at all. -/
theorem notMem_swapped (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    ((b, a) : target.V × target.V) ∉ target.edges := by
  intro hmem
  have h : ((b, a) : target.V × target.V) ∈
      target.edges.filter (fun e => e = (a, b) ∨ e = (b, a)) :=
    Multiset.mem_filter.mpr ⟨hmem, Or.inr rfl⟩
  rw [filter_eq_singleton hc hOne, Multiset.mem_singleton] at h
  exact hab (congrArg Prod.fst h).symm

/-- Any occurrence lying over the contracted pair *is* the contracted
occurrence. -/
theorem eq_contracted_of_coe_eq_pair (hc : (contracted : target.V × target.V) = (a, b))
    (hOne : num_edges target a b = 1) {f : target.edges}
    (hf : (f : target.V × target.V) = (a, b)) : f = contracted := by
  have hcount := count_pair_eq_one hc hOne
  have hcf : Multiset.count (f : target.V × target.V) target.edges = 1 := by
    rw [hf]; exact hcount
  have hcc : Multiset.count (contracted : target.V × target.V) target.edges = 1 := by
    rw [hc]; exact hcount
  have hbf := f.2.2
  have hbc := contracted.2.2
  apply (Multiset.coeEmbedding target.edges).injective
  simp only [Multiset.coeEmbedding_apply, Prod.mk.injEq]
  exact ⟨hf.trans hc.symm, by omega⟩

/-- A surviving occurrence lies over a kept pair. -/
theorem coe_mem_keptEdges (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {f : target.edges} (hne : f ≠ contracted) :
    (f : target.V × target.V) ∈ keptEdges target a b := by
  rw [GraphContraction.mem_keptEdges]
  refine ⟨Multiset.coe_mem, ?_⟩
  rintro (h | h)
  · exact hne (eq_contracted_of_coe_eq_pair hc hOne h)
  · exact notMem_swapped hc hab hOne (by rw [← h]; exact Multiset.coe_mem)

/-! ### The occurrence map into the contracted graph

The edge multiset of the contracted graph is the image of the kept pairs under
`fold`, and that image map is not injective: the pairs `(a, v)` and `(b, v)`
have the same image.  To turn a *surviving target occurrence* into an
occurrence of the contracted graph injectively, the occurrences at `b` are
listed after the occurrences at `a`. -/

/-- The index offset making `foldEdge` injective. -/
def foldIndex (a b : target.V) (q : target.V × target.V) (n : ℕ) : ℕ :=
  if q.1 = b then Multiset.count ((a, q.2) : target.V × target.V) target.edges + n
  else if q.2 = b then Multiset.count ((q.1, a) : target.V × target.V) target.edges + n
  else n

/-- The offset index really is a legal index for the image pair. -/
theorem foldIndex_lt (hab : a ≠ b) {q : target.V × target.V} {m : ℕ}
    (hkept : q ∈ keptEdges target a b) (hm : m < Multiset.count q target.edges) :
    foldIndex a b q m <
      Multiset.count (fold target hab q.1, fold target hab q.2) (contractEdges target hab) := by
  have hkeptDef : keptEdges target a b
      = target.edges.filter (fun e => ¬ (e = (a, b) ∨ e = (b, a))) := rfl
  have hce : contractEdges target hab
      = (keptEdges target a b).map (fun e => (fold target hab e.1, fold target hab e.2)) := rfl
  have hfoldab : fold target hab a = fold target hab b := by simp
  obtain ⟨hqE, hqkeep⟩ := (GraphContraction.mem_keptEdges (G := target)).mp hkept
  rw [hce, Multiset.count_map]
  obtain ⟨u, v⟩ := q
  have hne_ab : ¬ (u = a ∧ v = b) := by
    rintro ⟨rfl, rfl⟩; exact hqkeep (Or.inl rfl)
  have hne_ba : ¬ (u = b ∧ v = a) := by
    rintro ⟨rfl, rfl⟩; exact hqkeep (Or.inr rfl)
  have hloop : u ≠ v := by
    rintro rfl; exact target.loopless u hqE
  by_cases hub : u = b
  · subst hub
    have hva : v ≠ a := fun h => hne_ba ⟨rfl, h⟩
    have hvb : v ≠ u := Ne.symm hloop
    have hfi : foldIndex a u ((u, v) : target.V × target.V) m
        = Multiset.count ((a, v) : target.V × target.V) target.edges + m := by
      simp [foldIndex]
    have hcA : Multiset.count ((a, v) : target.V × target.V) (keptEdges target a u)
        = Multiset.count ((a, v) : target.V × target.V) target.edges := by
      rw [hkeptDef]
      refine Multiset.count_filter_of_pos ?_
      rintro (h | h)
      · exact hvb (congrArg Prod.snd h)
      · exact hab (congrArg Prod.fst h)
    have hcB : Multiset.count ((u, v) : target.V × target.V) (keptEdges target a u)
        = Multiset.count ((u, v) : target.V × target.V) target.edges := by
      rw [hkeptDef]
      exact Multiset.count_filter_of_pos hqkeep
    rw [hfi]
    refine lt_of_lt_of_le ?_ (two_counts_le_card_filter (keptEdges target a u) _
      (x := ((a, v) : target.V × target.V)) (y := ((u, v) : target.V × target.V))
      (fun h => hab (congrArg Prod.fst h)) (by rw [hfoldab]) rfl)
    rw [hcA, hcB]
    omega
  · by_cases hvb : v = b
    · subst hvb
      have hua : u ≠ a := fun h => hne_ab ⟨h, rfl⟩
      have hfi : foldIndex a v ((u, v) : target.V × target.V) m
          = Multiset.count ((u, a) : target.V × target.V) target.edges + m := by
        simp [foldIndex, hub]
      have hcA : Multiset.count ((u, a) : target.V × target.V) (keptEdges target a v)
          = Multiset.count ((u, a) : target.V × target.V) target.edges := by
        rw [hkeptDef]
        refine Multiset.count_filter_of_pos ?_
        rintro (h | h)
        · exact hab (congrArg Prod.snd h)
        · exact hub (congrArg Prod.fst h)
      have hcB : Multiset.count ((u, v) : target.V × target.V) (keptEdges target a v)
          = Multiset.count ((u, v) : target.V × target.V) target.edges := by
        rw [hkeptDef]
        exact Multiset.count_filter_of_pos hqkeep
      rw [hfi]
      refine lt_of_lt_of_le ?_ (two_counts_le_card_filter (keptEdges target a v) _
        (x := ((u, a) : target.V × target.V)) (y := ((u, v) : target.V × target.V))
        (fun h => hab (congrArg Prod.snd h)) (by rw [hfoldab]) rfl)
      rw [hcA, hcB]
      omega
    · have hfi : foldIndex a b ((u, v) : target.V × target.V) m = m := by
        simp [foldIndex, hub, hvb]
      have hcQ : Multiset.count ((u, v) : target.V × target.V) (keptEdges target a b)
          = Multiset.count ((u, v) : target.V × target.V) target.edges := by
        rw [hkeptDef]
        exact Multiset.count_filter_of_pos hqkeep
      rw [hfi]
      refine lt_of_lt_of_le ?_ (count_le_card_filter (keptEdges target a b) _
        (x := ((u, v) : target.V × target.V)) rfl)
      rw [hcQ]
      exact hm

/-! ### The occurrence map, injectively -/

/-- `foldIndex` is injective in the index. -/
theorem foldIndex_left_cancel (a b : target.V) (q : target.V × target.V) {m n : ℕ}
    (h : foldIndex a b q m = foldIndex a b q n) : m = n := by
  unfold foldIndex at h
  split_ifs at h <;> omega

/-- Value of `foldIndex` at a pair starting at the folded vertex. -/
theorem foldIndex_of_fst (a b : target.V) (q : target.V × target.V) (n : ℕ) (h : q.1 = b) :
    foldIndex a b q n = Multiset.count ((a, q.2) : target.V × target.V) target.edges + n := by
  simp only [foldIndex]
  rw [if_pos h]

/-- Value of `foldIndex` at a pair ending at the folded vertex. -/
theorem foldIndex_of_snd (a b : target.V) (q : target.V × target.V) (n : ℕ)
    (h1 : q.1 ≠ b) (h2 : q.2 = b) :
    foldIndex a b q n = Multiset.count ((q.1, a) : target.V × target.V) target.edges + n := by
  simp only [foldIndex]
  rw [if_neg h1, if_pos h2]

/-- Value of `foldIndex` away from the folded vertex. -/
theorem foldIndex_of_ne (a b : target.V) (q : target.V × target.V) (n : ℕ)
    (h1 : q.1 ≠ b) (h2 : q.2 ≠ b) : foldIndex a b q n = n := by
  simp only [foldIndex]
  rw [if_neg h1, if_neg h2]

/-- Two kept pairs with the same image and the same offset index are equal. -/
theorem pair_eq_of_fold_eq (hab : a ≠ b) {u₁ v₁ u₂ v₂ : target.V} {m₁ m₂ : ℕ}
    (hk₁ : ((u₁, v₁) : target.V × target.V) ∈ keptEdges target a b)
    (hk₂ : ((u₂, v₂) : target.V × target.V) ∈ keptEdges target a b)
    (hm₁ : m₁ < Multiset.count ((u₁, v₁) : target.V × target.V) target.edges)
    (hm₂ : m₂ < Multiset.count ((u₂, v₂) : target.V × target.V) target.edges)
    (hf1 : fold target hab u₁ = fold target hab u₂)
    (hf2 : fold target hab v₁ = fold target hab v₂)
    (hidx : foldIndex a b ((u₁, v₁) : target.V × target.V) m₁
      = foldIndex a b ((u₂, v₂) : target.V × target.V) m₂) :
    ((u₁, v₁) : target.V × target.V) = (u₂, v₂) := by
  obtain ⟨hqE₁, hqk₁⟩ := (GraphContraction.mem_keptEdges (G := target)).mp hk₁
  obtain ⟨hqE₂, hqk₂⟩ := (GraphContraction.mem_keptEdges (G := target)).mp hk₂
  rw [GraphContraction.fold_eq_fold_iff] at hf1 hf2
  rcases hf1 with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hf2 with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exfalso
      have hub : u₁ ≠ v₂ := fun h => hqk₁ (by simp [h])
      rw [foldIndex_of_ne _ _ ((u₁, v₁) : target.V × target.V) m₁ hub hab,
        foldIndex_of_snd _ _ ((u₁, v₂) : target.V × target.V) m₂ hub rfl] at hidx
      simp only at hidx
      omega
    · exfalso
      have hub : u₁ ≠ v₁ := fun h => hqk₂ (by simp [h])
      rw [foldIndex_of_snd _ _ ((u₁, v₁) : target.V × target.V) m₁ hub rfl,
        foldIndex_of_ne _ _ ((u₁, v₂) : target.V × target.V) m₂ hub hab] at hidx
      simp only at hidx
      omega
  · rcases hf2 with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exfalso
      have hvb : v₁ ≠ u₂ := fun h => hqk₁ (by simp [h])
      rw [foldIndex_of_ne _ _ ((u₁, v₁) : target.V × target.V) m₁ hab hvb,
        foldIndex_of_fst _ _ ((u₂, v₁) : target.V × target.V) m₂ rfl] at hidx
      simp only at hidx
      omega
    · exact absurd hqE₁ (target.loopless _)
    · exact (hqk₁ (by simp)).elim
  · rcases hf2 with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exfalso
      have hvb : v₁ ≠ u₁ := fun h => hqk₂ (by simp [h])
      rw [foldIndex_of_fst _ _ ((u₁, v₁) : target.V × target.V) m₁ rfl,
        foldIndex_of_ne _ _ ((u₂, v₁) : target.V × target.V) m₂ hab hvb] at hidx
      simp only at hidx
      omega
    · exact (hqk₁ (by simp)).elim
    · exact absurd hqE₁ (target.loopless _)

/-- A surviving target occurrence, seen as an occurrence of the contracted
graph. -/
def foldEdge (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (f : {f : target.edges // f ≠ contracted}) :
    (GraphContraction.contract target hab hOne).edges :=
  ⟨(fold target hab (f.1 : target.V × target.V).1,
      fold target hab (f.1 : target.V × target.V).2),
    ⟨foldIndex a b (f.1 : target.V × target.V) (f.1.2 : ℕ),
      foldIndex_lt hab (coe_mem_keptEdges hc hab hOne f.2) f.1.2.2⟩⟩

@[simp] theorem coe_foldEdge (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (f : {f : target.edges // f ≠ contracted}) :
    ((foldEdge hc hab hOne f : (GraphContraction.contract target hab hOne).edges) :
        (GraphContraction.contract target hab hOne).V ×
          (GraphContraction.contract target hab hOne).V)
      = (fold target hab (f.1 : target.V × target.V).1,
        fold target hab (f.1 : target.V × target.V).2) := rfl

theorem foldEdge_injective (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Function.Injective (foldEdge hc hab hOne) := by
  rintro ⟨⟨⟨u₁, v₁⟩, m₁⟩, h₁⟩ ⟨⟨⟨u₂, v₂⟩, m₂⟩, h₂⟩ hEq
  have hk₁ : ((u₁, v₁) : target.V × target.V) ∈ keptEdges target a b :=
    coe_mem_keptEdges hc hab hOne h₁
  have hk₂ : ((u₂, v₂) : target.V × target.V) ∈ keptEdges target a b :=
    coe_mem_keptEdges hc hab hOne h₂
  have hfst : ((fold target hab u₁, fold target hab v₁) :
        (GraphContraction.contract target hab hOne).V ×
          (GraphContraction.contract target hab hOne).V)
      = (fold target hab u₂, fold target hab v₂) :=
    congrArg (fun x : (GraphContraction.contract target hab hOne).edges => x.1) hEq
  have hidx : foldIndex a b ((u₁, v₁) : target.V × target.V) (m₁ : ℕ)
      = foldIndex a b ((u₂, v₂) : target.V × target.V) (m₂ : ℕ) :=
    congrArg (fun x : (GraphContraction.contract target hab hOne).edges => (x.2 : ℕ)) hEq
  have hf1 : fold target hab u₁ = fold target hab u₂ := congrArg Prod.fst hfst
  have hf2 : fold target hab v₁ = fold target hab v₂ := congrArg Prod.snd hfst
  have hpair := pair_eq_of_fold_eq hab hk₁ hk₂ m₁.2 m₂.2 hf1 hf2 hidx
  have hval : (m₁ : ℕ) = (m₂ : ℕ) := by
    refine foldIndex_left_cancel a b ((u₂, v₂) : target.V × target.V) ?_
    rw [← hidx]
    exact congrArg (fun q => foldIndex a b q (m₁ : ℕ)) hpair.symm
  apply Subtype.ext
  apply (Multiset.coeEmbedding target.edges).injective
  show ((((u₁, v₁) : target.V × target.V), (m₁ : ℕ)) : (target.V × target.V) × ℕ)
      = (((u₂, v₂) : target.V × target.V), (m₂ : ℕ))
  exact Prod.ext hpair hval

/-! ### The occurrence map is a bijection -/

theorem card_surviving_eq (_hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Fintype.card {f : target.edges // f ≠ contracted}
      = Fintype.card ((GraphContraction.contract target hab hOne).edges) := by
  have h1 : Fintype.card {f : target.edges // f ≠ contracted}
      = Fintype.card (target.edges) - 1 := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  rw [h1, Multiset.card_coe, Multiset.card_coe, GraphContraction.card_edges_contract]

theorem foldEdge_bijective (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Function.Bijective (foldEdge hc hab hOne) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨foldEdge_injective hc hab hOne, card_surviving_eq hc hab hOne⟩

/-- Surviving target occurrences correspond bijectively to the occurrences of
the contracted graph. -/
noncomputable def foldEdgeEquiv (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    {f : target.edges // f ≠ contracted} ≃ (GraphContraction.contract target hab hOne).edges :=
  Equiv.ofBijective _ (foldEdge_bijective hc hab hOne)

/-- The surviving target occurrence underlying an occurrence of the contracted
graph. -/
noncomputable def unfoldEdge (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : (GraphContraction.contract target hab hOne).edges) : target.edges :=
  ((foldEdgeEquiv hc hab hOne).symm e).1

theorem unfoldEdge_ne_contracted (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : (GraphContraction.contract target hab hOne).edges) :
    unfoldEdge hc hab hOne e ≠ contracted :=
  ((foldEdgeEquiv hc hab hOne).symm e).2

/-- The chosen surviving occurrence really lies over the given occurrence of
the contracted graph. -/
theorem fold_unfoldEdge (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : (GraphContraction.contract target hab hOne).edges) :
    ((fold target hab (unfoldEdge hc hab hOne e : target.V × target.V).1,
        fold target hab (unfoldEdge hc hab hOne e : target.V × target.V).2) :
      (GraphContraction.contract target hab hOne).V ×
        (GraphContraction.contract target hab hOne).V)
      = (e : (GraphContraction.contract target hab hOne).V ×
          (GraphContraction.contract target hab hOne).V) :=
  congrArg (fun x : (GraphContraction.contract target hab hOne).edges => x.1)
    ((foldEdgeEquiv hc hab hOne).apply_symm_apply e)

theorem unfoldEdge_foldEdge (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (f : {f : target.edges // f ≠ contracted}) :
    unfoldEdge hc hab hOne (foldEdge hc hab hOne f) = f.1 :=
  congrArg Subtype.val ((foldEdgeEquiv hc hab hOne).symm_apply_apply f)

/-! ### (1) The contracted gluing datum -/

/-- The vertex partitions of the contracted datum: above the merged vertex the
join of the two endpoint partitions, elsewhere the old partition. -/
noncomputable def contractVertexPartition (data : GluingDatum target degree) (a b : target.V)
    (y : GraphContraction.Vertex target b) : SheetPartition degree :=
  if (y : target.V) = a then
    SheetPartition.join (data.vertexPartition a) (data.vertexPartition b)
  else data.vertexPartition (y : target.V)

theorem contractVertexPartition_merge (data : GluingDatum target degree) (a b : target.V)
    (hab : a ≠ b) :
    contractVertexPartition data a b ⟨a, hab⟩
      = SheetPartition.join (data.vertexPartition a) (data.vertexPartition b) :=
  if_pos rfl

theorem contractVertexPartition_of_ne (data : GluingDatum target degree) (a b : target.V)
    {y : GraphContraction.Vertex target b} (h : (y : target.V) ≠ a) :
    contractVertexPartition data a b y = data.vertexPartition (y : target.V) :=
  if_neg h

/-- Every old vertex partition refines the vertex partition sitting above its
image.  Away from the merged vertex this is an equality; at the merged vertex
it is one half of the join. -/
theorem vertexPartition_refines (data : GluingDatum target degree) (hab : a ≠ b) (v : target.V) :
    (data.vertexPartition v).Refines
      (contractVertexPartition data a b (fold target hab v)) := by
  by_cases hvb : v = b
  · have h1 : fold target hab v = ⟨a, hab⟩ := by
      rw [hvb]; exact GraphContraction.fold_self target hab
    have h2 : data.vertexPartition v = data.vertexPartition b := by rw [hvb]
    rw [h1, contractVertexPartition_merge, h2]
    exact SheetPartition.right_refines_join _ _
  · rw [GraphContraction.fold_of_ne target hab hvb]
    by_cases hva : v = a
    · have h2 : contractVertexPartition data a b ⟨v, hvb⟩
          = SheetPartition.join (data.vertexPartition a) (data.vertexPartition b) := if_pos hva
      rw [h2, hva]
      exact SheetPartition.left_refines_join _ _
    · rw [contractVertexPartition_of_ne data a b (y := ⟨v, hvb⟩) hva]
      exact SheetPartition.Refines.refl _

/-- The limit gluing datum of Draisma--Vargas Part I (`def-limit-gluing`): the
gluing datum obtained by contracting one target edge occurrence. -/
noncomputable def contractDatum (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    GluingDatum (GraphContraction.contract target hab hOne) degree where
  degree_pos := data.degree_pos
  vertexPartition := contractVertexPartition data a b
  edgePartition := fun e => data.edgePartition (unfoldEdge hc hab hOne e)
  refines_left := by
    intro e
    have h := congrArg Prod.fst (fold_unfoldEdge hc hab hOne e)
    rw [← h]
    exact (data.refines_left (unfoldEdge hc hab hOne e)).trans
      (vertexPartition_refines data hab _)
  refines_right := by
    intro e
    have h := congrArg Prod.snd (fold_unfoldEdge hc hab hOne e)
    rw [← h]
    exact (data.refines_right (unfoldEdge hc hab hOne e)).trans
      (vertexPartition_refines data hab _)

@[simp] theorem contractDatum_vertexPartition (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    (contractDatum data hc hab hOne).vertexPartition = contractVertexPartition data a b := rfl

@[simp] theorem contractDatum_edgePartition (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : (GraphContraction.contract target hab hOne).edges) :
    (contractDatum data hc hab hOne).edgePartition e
      = data.edgePartition (unfoldEdge hc hab hOne e) := rfl

/-- A surviving target occurrence keeps its own sheet partition. -/
theorem contractDatum_edgePartition_foldEdge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (f : {f : target.edges // f ≠ contracted}) :
    (contractDatum data hc hab hOne).edgePartition (foldEdge hc hab hOne f)
      = data.edgePartition f.1 := by
  rw [contractDatum_edgePartition, unfoldEdge_foldEdge]

/-! ### (2) The source correspondence -/

/-- Source vertices of the original datum map onto source vertices of the
contracted datum. -/
noncomputable def sourceVertexMap (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (x : data.SourceVertex) :
    (contractDatum data hc hab hOne).SourceVertex :=
  (contractDatum data hc hab hOne).sourceEndpoint (fold target hab x.1.1) x.1.2

/-- Changing the chosen sheet inside its old block does not change the image
source vertex. -/
theorem sourceEndpoint_repr (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (u : target.V) (i : Fin degree) :
    (contractDatum data hc hab hOne).sourceEndpoint (fold target hab u) i
      = (contractDatum data hc hab hOne).sourceEndpoint (fold target hab u)
        ((data.vertexPartition u).repr i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · have h : (contractVertexPartition data a b (fold target hab u)).Rel i
        ((data.vertexPartition u).repr i) :=
      (vertexPartition_refines data hab u).rel ((data.vertexPartition u).rel_repr_right i)
    exact h

theorem sourceVertexMap_surjective (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Function.Surjective (sourceVertexMap data hc hab hOne) := by
  rintro ⟨⟨⟨u, hu⟩, i⟩, hy⟩
  refine ⟨data.sourceEndpoint u i, ?_⟩
  have hfold : fold target hab u = (⟨u, hu⟩ : GraphContraction.Vertex target b) :=
    GraphContraction.fold_of_ne target hab hu
  have hrel : (contractVertexPartition data a b (fold target hab u)).Rel
      ((data.vertexPartition u).repr i) i :=
    (vertexPartition_refines data hab u).rel ((data.vertexPartition u).rel_repr_left i)
  rw [SheetPartition.rel_iff, hfold] at hrel
  apply Subtype.ext
  refine Prod.ext hfold ?_
  show (contractVertexPartition data a b (fold target hab u)).repr
      ((data.vertexPartition u).repr i) = i
  rw [hfold, hrel]
  exact hy

/-- Source edge occurrences away from the contracted target occurrence map to
source edge occurrences of the contracted datum. -/
noncomputable def sourceEdgeMap (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : {e : data.SourceEdge // e.1.1 ≠ contracted}) :
    (contractDatum data hc hab hOne).SourceEdge :=
  ⟨(foldEdge hc hab hOne ⟨e.1.1.1, e.2⟩, e.1.1.2), by
    rw [contractDatum_edgePartition_foldEdge]
    exact e.1.2⟩

theorem sourceEdgeMap_injective (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Function.Injective (sourceEdgeMap data hc hab hOne) := by
  intro e₁ e₂ h
  have h1 := congrArg
    (fun z : (contractDatum data hc hab hOne).SourceEdge => z.1.1) h
  have h2 := congrArg
    (fun z : (contractDatum data hc hab hOne).SourceEdge => z.1.2) h
  have hf : e₁.1.1.1 = e₂.1.1.1 :=
    congrArg Subtype.val (foldEdge_injective hc hab hOne h1)
  exact Subtype.ext (Subtype.ext (Prod.ext hf h2))

/-- The endpoints of a mapped source edge occurrence are the images of its
endpoints. -/
theorem sourceEnds_sourceEdgeMap (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : {e : data.SourceEdge // e.1.1 ≠ contracted}) :
    (contractDatum data hc hab hOne).sourceEnds (sourceEdgeMap data hc hab hOne e)
      = (sourceVertexMap data hc hab hOne (data.sourceEnds e.1).1,
        sourceVertexMap data hc hab hOne (data.sourceEnds e.1).2) :=
  Prod.ext (sourceEndpoint_repr data hc hab hOne _ _)
    (sourceEndpoint_repr data hc hab hOne _ _)

/-- Above the contracted target occurrence the two source endpoints have the
same image.  This is exactly the join condition: the two endpoint blocks are
joined above the merged vertex. -/
theorem sourceVertexMap_sourceEnds_eq_of_contracted (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (e : data.SourceEdge) (he : e.1.1 = contracted) :
    sourceVertexMap data hc hab hOne (data.sourceEnds e).1
      = sourceVertexMap data hc hab hOne (data.sourceEnds e).2 := by
  have hpair : (e.1.1 : target.V × target.V) = (a, b) := by rw [he]; exact hc
  have hA : (e.1.1 : target.V × target.V).1 = a := by rw [hpair]
  have hB : (e.1.1 : target.V × target.V).2 = b := by rw [hpair]
  have key : ∀ u : target.V, sourceVertexMap data hc hab hOne (data.sourceEndpoint u e.1.2)
      = (contractDatum data hc hab hOne).sourceEndpoint (fold target hab u)
        ((data.vertexPartition u).repr e.1.2) := fun _ => rfl
  show sourceVertexMap data hc hab hOne
      (data.sourceEndpoint (e.1.1 : target.V × target.V).1 e.1.2)
    = sourceVertexMap data hc hab hOne
      (data.sourceEndpoint (e.1.1 : target.V × target.V).2 e.1.2)
  rw [key, key, hA, hB, GraphContraction.fold_a, GraphContraction.fold_self]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (contractVertexPartition data a b ⟨a, hab⟩).repr
        ((data.vertexPartition a).repr e.1.2)
      = (contractVertexPartition data a b ⟨a, hab⟩).repr
        ((data.vertexPartition b).repr e.1.2)
    rw [contractVertexPartition_merge]
    have hL : (SheetPartition.join (data.vertexPartition a) (data.vertexPartition b)).repr
        ((data.vertexPartition a).repr e.1.2)
        = (SheetPartition.join (data.vertexPartition a) (data.vertexPartition b)).repr e.1.2 :=
      (SheetPartition.left_refines_join (data.vertexPartition a)
        (data.vertexPartition b)).rel ((data.vertexPartition a).rel_repr_left e.1.2)
    have hR : (SheetPartition.join (data.vertexPartition a) (data.vertexPartition b)).repr
        ((data.vertexPartition b).repr e.1.2)
        = (SheetPartition.join (data.vertexPartition a) (data.vertexPartition b)).repr e.1.2 :=
      (SheetPartition.right_refines_join (data.vertexPartition a)
        (data.vertexPartition b)).rel ((data.vertexPartition b).rel_repr_left e.1.2)
    rw [hL, hR]

/-! ### (3) Connectivity of the contracted source -/

/-- Contracting a target edge preserves connectedness of the quotient source.
A separating set downstairs is pulled back along `sourceVertexMap`; the
crossing occurrence found upstairs cannot lie over the contracted target
occurrence, because such an occurrence has both endpoints in the same
contracted source vertex. -/
theorem connected_contractDatum (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hConnected : data.Connected) :
    (contractDatum data hc hab hOne).Connected := by
  classical
  intro T hT
  obtain ⟨x₀, y₀, hx₀, hy₀⟩ := hT
  set S : Finset data.SourceVertex :=
    Finset.univ.filter (fun v => sourceVertexMap data hc hab hOne v ∈ T) with hSdef
  have hmemS : ∀ v : data.SourceVertex,
      v ∈ S ↔ sourceVertexMap data hc hab hOne v ∈ T := by
    intro v
    rw [hSdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩
  obtain ⟨x, hx⟩ := sourceVertexMap_surjective data hc hab hOne x₀
  obtain ⟨y, hy⟩ := sourceVertexMap_surjective data hc hab hOne y₀
  have hxS : x ∈ S := (hmemS x).mpr (by rw [hx]; exact hx₀)
  have hyS : y ∉ S := fun h => hy₀ (by rw [← hy]; exact (hmemS y).mp h)
  obtain ⟨v, hvS, w, hwS, hpos⟩ := hConnected S ⟨x, y, hxS, hyS⟩
  have hvw : sourceVertexMap data hc hab hOne v ≠ sourceVertexMap data hc hab hOne w := by
    intro h
    exact hwS ((hmemS w).mpr (h ▸ (hmemS v).mp hvS))
  obtain ⟨edge, hedgeMem, hends⟩ :=
    GraphContraction.exists_mem_edges_of_num_edges_pos data.sourceGraph v w hpos
  obtain ⟨se, -, hse⟩ := Multiset.mem_map.mp
    (show edge ∈ (Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds from hedgeMem)
  have hne : se.1.1 ≠ contracted := by
    intro hcon
    have hsame := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne se hcon
    rw [hse] at hsame
    rcases hends with rfl | rfl
    · exact hvw hsame
    · exact hvw hsame.symm
  have hmem : (contractDatum data hc hab hOne).sourceEnds
      (sourceEdgeMap data hc hab hOne ⟨se, hne⟩)
      ∈ (contractDatum data hc hab hOne).sourceGraph.edges :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ _)
  rw [sourceEnds_sourceEdgeMap, hse] at hmem
  refine ⟨sourceVertexMap data hc hab hOne v, (hmemS v).mp hvS,
    sourceVertexMap data hc hab hOne w, fun hcon => hwS ((hmemS w).mpr hcon), ?_⟩
  rcases hends with rfl | rfl
  · exact GraphContraction.num_edges_pos_of_mem_edges
      (contractDatum data hc hab hOne).sourceGraph _ _ hmem
  · exact GraphContraction.num_edges_pos_of_mem_edges'
      (contractDatum data hc hab hOne).sourceGraph _ _ hmem

/-! ### (4) Riemann--Hurwitz away from the merged vertex

Away from the merged vertex nothing changes: the vertex partition is literally
the old one and the incident occurrences are carried bijectively by `foldEdge`,
so the local Riemann--Hurwitz inequality is inherited verbatim.  (At the merged
vertex the inequality is genuine Draisma--Vargas mathematics and is not proved
here.) -/

/-- Membership in the incident-occurrence star. -/
theorem mem_incidentEdges_iff {G : CFGraph} (vertex : G.V) (edge : G.edges) :
    edge ∈ GluingDatum.incidentEdges vertex ↔
      (edge : G.V × G.V).1 = vertex ∨ (edge : G.V × G.V).2 = vertex := by
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The contracted occurrence is not incident to a vertex other than its two
endpoints. -/
theorem ne_contracted_of_mem_incidentEdges
    (hc : (contracted : target.V × target.V) = (a, b)) {u : target.V} (hub : u ≠ b)
    (hua : u ≠ a) {f : target.edges} (hf : f ∈ GluingDatum.incidentEdges u) :
    f ≠ contracted := by
  intro hcon
  have hpair : (f : target.V × target.V) = (a, b) := by rw [hcon]; exact hc
  rcases (mem_incidentEdges_iff u f).mp hf with h | h
  · exact hua (by rw [← h, hpair])
  · exact hub (by rw [← h, hpair])

/-- `foldEdge` carries the occurrences incident to an unmerged vertex to the
occurrences incident to its image. -/
theorem mem_incidentEdges_foldEdge (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1) {u : target.V} (hub : u ≠ b)
    {f : target.edges} (hne : f ≠ contracted) (hf : f ∈ GluingDatum.incidentEdges u) :
    foldEdge hc hab hOne ⟨f, hne⟩ ∈ GluingDatum.incidentEdges
      (⟨u, hub⟩ : (GraphContraction.contract target hab hOne).V) := by
  have hfold : fold target hab u = (⟨u, hub⟩ : GraphContraction.Vertex target b) :=
    GraphContraction.fold_of_ne target hab hub
  refine (mem_incidentEdges_iff _ _).mpr ?_
  rcases (mem_incidentEdges_iff u f).mp hf with h | h
  · exact Or.inl (show fold target hab (f : target.V × target.V).1 = _ by rw [h, hfold])
  · exact Or.inr (show fold target hab (f : target.V × target.V).2 = _ by rw [h, hfold])

/-- The inverse direction: the chosen preimage of an incident occurrence is
incident. -/
theorem mem_incidentEdges_unfoldEdge (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1) {u : target.V} (hub : u ≠ b) (hua : u ≠ a)
    {e : (GraphContraction.contract target hab hOne).edges}
    (he : e ∈ GluingDatum.incidentEdges (target := GraphContraction.contract target hab hOne)
      ⟨u, hub⟩) :
    unfoldEdge hc hab hOne e ∈ GluingDatum.incidentEdges u := by
  have hf := fold_unfoldEdge hc hab hOne e
  refine (mem_incidentEdges_iff u _).mpr ?_
  rcases (mem_incidentEdges_iff _ e).mp he with h | h
  · have h1 : fold target hab (unfoldEdge hc hab hOne e : target.V × target.V).1
        = (⟨u, hub⟩ : GraphContraction.Vertex target b) := (congrArg Prod.fst hf).trans h
    rcases (GraphContraction.fold_eq_iff target hab _ _).mp h1 with h2 | ⟨h2, -⟩
    · exact Or.inl h2
    · exact absurd h2 hua
  · have h1 : fold target hab (unfoldEdge hc hab hOne e : target.V × target.V).2
        = (⟨u, hub⟩ : GraphContraction.Vertex target b) := (congrArg Prod.snd hf).trans h
    rcases (GraphContraction.fold_eq_iff target hab _ _).mp h1 with h2 | ⟨h2, -⟩
    · exact Or.inr h2
    · exact absurd h2 hua

theorem foldEdge_unfoldEdge (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (e : (GraphContraction.contract target hab hOne).edges)
    (h : unfoldEdge hc hab hOne e ≠ contracted) :
    foldEdge hc hab hOne ⟨unfoldEdge hc hab hOne e, h⟩ = e := by
  have hsub : (⟨unfoldEdge hc hab hOne e, h⟩ : {f : target.edges // f ≠ contracted})
      = (foldEdgeEquiv hc hab hOne).symm e := Subtype.ext rfl
  rw [hsub]
  exact (foldEdgeEquiv hc hab hOne).apply_symm_apply e

/-- The star of an unmerged target vertex is unchanged by the contraction. -/
theorem card_incidentEdges_contract_of_ne (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1) {u : target.V} (hub : u ≠ b) (hua : u ≠ a) :
    (GluingDatum.incidentEdges u).card
      = (GluingDatum.incidentEdges (target := GraphContraction.contract target hab hOne)
        ⟨u, hub⟩).card :=
  Finset.card_bij
    (fun f hf => foldEdge hc hab hOne ⟨f, ne_contracted_of_mem_incidentEdges hc hub hua hf⟩)
    (fun _ hf => mem_incidentEdges_foldEdge hc hab hOne hub _ hf)
    (fun _ _ _ _ heq => congrArg Subtype.val (foldEdge_injective hc hab hOne heq))
    (fun e he => ⟨unfoldEdge hc hab hOne e,
      mem_incidentEdges_unfoldEdge hc hab hOne hub hua he,
      foldEdge_unfoldEdge hc hab hOne e _⟩)

/-- The induced block counts along the star of an unmerged target vertex are
unchanged by the contraction. -/
theorem sum_blockCountWithin_contract_of_ne (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {u : target.V} (hub : u ≠ b) (hua : u ≠ a)
    (sheet : Fin degree) :
    (∑ edge ∈ GluingDatum.incidentEdges u,
      ((data.edgePartition edge).blockCountWithin (data.vertexPartition u) sheet : ℤ))
    = ∑ edge ∈ GluingDatum.incidentEdges (target := GraphContraction.contract target hab hOne)
        ⟨u, hub⟩,
      (((contractDatum data hc hab hOne).edgePartition edge).blockCountWithin
        ((contractDatum data hc hab hOne).vertexPartition ⟨u, hub⟩) sheet : ℤ) := by
  have hvp : (contractDatum data hc hab hOne).vertexPartition
      (⟨u, hub⟩ : (GraphContraction.contract target hab hOne).V) = data.vertexPartition u :=
    contractVertexPartition_of_ne data a b (y := ⟨u, hub⟩) hua
  refine Finset.sum_bij
    (fun f hf => foldEdge hc hab hOne ⟨f, ne_contracted_of_mem_incidentEdges hc hub hua hf⟩)
    (fun _ hf => mem_incidentEdges_foldEdge hc hab hOne hub _ hf)
    (fun _ _ _ _ heq => congrArg Subtype.val (foldEdge_injective hc hab hOne heq))
    (fun e he => ⟨unfoldEdge hc hab hOne e,
      mem_incidentEdges_unfoldEdge hc hab hOne hub hua he,
      foldEdge_unfoldEdge hc hab hOne e _⟩) ?_
  intro f hf
  rw [contractDatum_edgePartition_foldEdge, hvp]

/-- Away from the merged vertex the local Riemann--Hurwitz condition is
inherited verbatim. -/
theorem riemannHurwitzAtTargetVertex_contractDatum_of_ne (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {u : target.V} (hub : u ≠ b) (hua : u ≠ a)
    (hRH : data.RiemannHurwitzAtTargetVertex u) :
    (contractDatum data hc hab hOne).RiemannHurwitzAtTargetVertex
      (⟨u, hub⟩ : (GraphContraction.contract target hab hOne).V) := by
  have hvp : (contractDatum data hc hab hOne).vertexPartition
      (⟨u, hub⟩ : (GraphContraction.contract target hab hOne).V) = data.vertexPartition u :=
    contractVertexPartition_of_ne data a b (y := ⟨u, hub⟩) hua
  intro sheet
  rw [← sum_blockCountWithin_contract_of_ne data hc hab hOne hub hua sheet,
    ← card_incidentEdges_contract_of_ne hc hab hOne hub hua, hvp]
  exact hRH sheet

/-! ### The canonical instantiation at a chosen target occurrence

The development above carries the endpoints `a`, `b` of the contracted
occurrence as separate parameters together with `hc`.  Reading them off the
occurrence itself makes `hc` a `rfl` and `hab` automatic. -/

/-- The two endpoints of a target occurrence are distinct: the target graph is
loopless. -/
theorem fst_ne_snd (edge : target.edges) :
    (edge : target.V × target.V).1 ≠ (edge : target.V × target.V).2 :=
  ne_of_coe_eq_pair (contracted := edge) (a := (edge : target.V × target.V).1)
    (b := (edge : target.V × target.V).2) rfl

/-- The target graph with one occurrence contracted. -/
def contractTarget (edge : target.edges)
    (hOne : num_edges target (edge : target.V × target.V).1
      (edge : target.V × target.V).2 = 1) : CFGraph :=
  GraphContraction.contract target (fst_ne_snd edge) hOne

/-- The limit gluing datum of Draisma--Vargas Part I at a chosen target
occurrence: the limit of a gluing datum obtained by contracting that
occurrence. -/
noncomputable def contractDatumAt (data : GluingDatum target degree) (edge : target.edges)
    (hOne : num_edges target (edge : target.V × target.V).1
      (edge : target.V × target.V).2 = 1) :
    GluingDatum (contractTarget edge hOne) degree :=
  contractDatum data (contracted := edge) (a := (edge : target.V × target.V).1)
    (b := (edge : target.V × target.V).2) rfl (fst_ne_snd edge) hOne

/-- Contracting a target occurrence preserves connectedness of the quotient
source. -/
theorem connected_contractDatumAt (data : GluingDatum target degree) (edge : target.edges)
    (hOne : num_edges target (edge : target.V × target.V).1
      (edge : target.V × target.V).2 = 1) (hConnected : data.Connected) :
    (contractDatumAt data edge hOne).Connected :=
  connected_contractDatum data _ _ hOne hConnected

end GluingContraction

end DraismaVargas.Infrastructure
