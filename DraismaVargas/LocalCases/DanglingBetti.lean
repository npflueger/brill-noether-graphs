module

public import DraismaVargas.LocalCases.PrunedSource

@[expose] public section

/-!
# Dangling deletion preserves the first Betti number

`DraismaVargas.LocalCases.PrunedSource` builds the pruned source `Γ` as an
actual `CFGraph` and gives it the two invariants an Euler count consumes: the
occurrence count `m = (nonDanglingEdges data).card` and the first Betti number
`cyclomatic Γ = m - n + c`.  Saturating the Draisma--Vargas Euler bound of
`DraismaVargas.LocalCases.Trivalence` needs, as one of its two inputs, the
identification of that Betti number with `genus data.sourceGraph`
(`DraismaVargas.LocalCases.TrivalenceClosure` uses it).  This module supplies
it:

```lean
cyclomatic (prunedSource data) = genus data.sourceGraph
```

under connectedness of the quotient source, which is the first component of
`GluingDatum.Valid`.

## Why it is true

Deleting one edge occurrence changes `|E| - |V| + c` by `-1` in the occurrence
count and by `+1` in the component count **exactly when the occurrence is a
bridge**, and by `-1` and `0` otherwise.  A dangling occurrence is a bridge:
its `W4StableSource.DanglingSide` certificate carries a
`Utilities.SeparatingEdgeCut`, i.e. a vertex set containing one endpoint,
missing the other, and crossed by no other occurrence at all.  So each of the
deletions performed by `W4StableSource.nonDanglingEdges` raises the component
count by exactly one and the two changes cancel, leaving `cyclomatic`
unchanged.  Since the quotient source is connected, `cyclomatic` there is
`genus` (`PrunedSource.cyclomatic_eq_genus_of_connected`).

**Which route.**  `DanglingDescent.bridge_split` is *not* used.  Its hypothesis
is the tree count `|E| + 1 = |V|` of the whole graph, which the quotient source
does not satisfy; and it is anyway a statement about `deletePair`, which
removes *every* occurrence joining the two endpoints rather than the single
distinguished one.  What is used instead is the separating cut stored in
`IsDangling` directly: `IsCutOccurrence` below repackages
`Utilities.SeparatingEdgeCut.cross_num_edges`, and
`noCross_of_isCutOccurrence` turns it into the statement that no *other*
occurrence crosses the cut, which is exactly what makes the two endpoints
unreachable after the deletion.

## The count

* `IsCutOccurrence` — an occurrence with a separating cut around one endpoint.
* `componentCount_cons_add_one_le` — deleting a cut occurrence raises the
  component count by **at least** one; this is the half an Euler identity
  cannot supply, and it is where the cut is spent.
* `PrunedSource.componentCount_le_componentCount_cons_add_one` — deleting any
  occurrence raises the component count by at most one.
* `componentCount_subEdges_of_cut` — the induction over a whole multiset of cut
  occurrences: `c(G - D) = c(G) + |D|`.
* `isCutOccurrence_of_isDangling` — a dangling quotient-source occurrence is a
  cut occurrence.
* `cyclomatic_prunedSource_eq_genus_sourceGraph` — the deliverable.

Note that `genus` in this development is `|E| - |V| + 1` unconditionally, hence
the first Betti number only for a connected graph.  It is therefore used only
on `data.sourceGraph`, which `GluingDatum.Valid` makes connected; the pruned
source is generally disconnected and only ever carries `cyclomatic`.

## Shared machinery

The graph-on-a-submultiset constructor `subEdges` and the component-counting
steps `reach_cons_cases`, `repOf`, `component_repOf` and
`componentCount_le_componentCount_cons_add_one` are not local to this module:
they live in `DraismaVargas.LocalCases.PrunedSource`, which this module
imports.
-/

namespace DraismaVargas.LocalCases.DanglingBetti

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.LocalCases.PrunedSource

universe u

/-! ## Cut occurrences

An occurrence is a *cut occurrence* when some vertex set contains one of its
endpoints, misses the other, and is crossed by no occurrence except this one.
This is exactly the content of `Utilities.SeparatingEdgeCut`, which is what a
`W4StableSource.DanglingSide` certificate carries. -/

section Cut

/-- **A cut occurrence.**  `S` contains `p.1`, misses `p.2`, and the only
occurrence of `G` running between `S` and its complement is the single
occurrence `p`. -/
def IsCutOccurrence (G : CFGraph.{u}) (p : G.V × G.V) : Prop :=
  ∃ S : Finset G.V, p.1 ∈ S ∧ p.2 ∉ S ∧
    ∀ a b : G.V, a ∈ S → b ∉ S →
      num_edges G a b = if a = p.1 ∧ b = p.2 then 1 else 0

/-- A recorded occurrence contributes to the multiplicity of its own two
endpoints. -/
private theorem one_le_num_edges_of_mem (G : CFGraph.{u}) {q : G.V × G.V}
    (hq : q ∈ G.edges) : 1 ≤ num_edges G q.1 q.2 :=
  Multiset.card_pos_iff_exists_mem.2 ⟨q, Multiset.mem_filter.2 ⟨hq, Or.inl rfl⟩⟩

/-- If a second occurrence with the same two endpoints, in either orientation,
survives alongside `p`, then the multiplicity of that endpoint pair is at least
two. -/
private theorem two_le_num_edges_of_mem (G : CFGraph.{u}) (p : G.V × G.V)
    (t : Multiset (G.V × G.V)) (hLe : p ::ₘ t ≤ G.edges)
    {q : G.V × G.V} (hq : q ∈ t) (hqp : q = p ∨ q = (p.2, p.1)) :
    2 ≤ num_edges G p.1 p.2 := by
  classical
  have hTail : q ∈ t.filter fun e ↦ e = (p.1, p.2) ∨ e = (p.2, p.1) := by
    refine Multiset.mem_filter.2 ⟨hq, ?_⟩
    rcases hqp with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hTailPos :
      0 < Multiset.card (t.filter fun e ↦ e = (p.1, p.2) ∨ e = (p.2, p.1)) :=
    Multiset.card_pos_iff_exists_mem.2 ⟨q, hTail⟩
  have hCons :
      Multiset.card ((p ::ₘ t).filter fun e ↦ e = (p.1, p.2) ∨ e = (p.2, p.1))
        = Multiset.card (t.filter fun e ↦ e = (p.1, p.2) ∨ e = (p.2, p.1)) + 1 := by
    rw [Multiset.filter_cons,
      ite_eq_left (show p = (p.1, p.2) ∨ p = (p.2, p.1) from Or.inl rfl),
      Multiset.card_add, Multiset.card_singleton]
    omega
  have hMono :
      Multiset.card ((p ::ₘ t).filter fun e ↦ e = (p.1, p.2) ∨ e = (p.2, p.1))
        ≤ num_edges G p.1 p.2 :=
    Multiset.card_le_card (Multiset.filter_le_filter _ hLe)
  omega

/-- **A cut occurrence is the only occurrence crossing its cut.**  Once the
single crossing occurrence is removed, every remaining occurrence has both
endpoints on the same side. -/
theorem noCross_of_isCutOccurrence (G : CFGraph.{u}) (p : G.V × G.V)
    (S : Finset G.V)
    (hCross : ∀ a b : G.V, a ∈ S → b ∉ S →
      num_edges G a b = if a = p.1 ∧ b = p.2 then 1 else 0)
    (t : Multiset (G.V × G.V)) (hLe : p ::ₘ t ≤ G.edges) :
    ∀ q ∈ t, (q.1 ∈ S ↔ q.2 ∈ S) := by
  classical
  intro q hq
  have hqG : q ∈ G.edges :=
    Multiset.mem_of_le hLe (Multiset.mem_cons_of_mem hq)
  constructor
  · intro h1
    by_contra h2
    have hOne : num_edges G q.1 q.2 = if q.1 = p.1 ∧ q.2 = p.2 then 1 else 0 :=
      hCross q.1 q.2 h1 h2
    have hPos : 1 ≤ num_edges G q.1 q.2 := one_le_num_edges_of_mem G hqG
    by_cases hIf : q.1 = p.1 ∧ q.2 = p.2
    · have hqp : q = p := Prod.ext hIf.1 hIf.2
      rw [ite_eq_left hIf] at hOne
      have hTwo := two_le_num_edges_of_mem G p t hLe hq (Or.inl hqp)
      rw [hqp] at hOne
      omega
    · rw [ite_eq_right hIf] at hOne
      omega
  · intro h2
    by_contra h1
    have hOne : num_edges G q.2 q.1 = if q.2 = p.1 ∧ q.1 = p.2 then 1 else 0 :=
      hCross q.2 q.1 h2 h1
    have hPos : 1 ≤ num_edges G q.2 q.1 := by
      rw [num_edges_symmetric]
      exact one_le_num_edges_of_mem G hqG
    by_cases hIf : q.2 = p.1 ∧ q.1 = p.2
    · have hqp : q = (p.2, p.1) := Prod.ext hIf.2 hIf.1
      rw [ite_eq_left hIf] at hOne
      have hTwo := two_le_num_edges_of_mem G p t hLe hq (Or.inr hqp)
      rw [show p.1 = q.2 from hIf.1.symm, show p.2 = q.1 from hIf.2.symm] at hTwo
      omega
    · rw [ite_eq_right hIf] at hOne
      omega

end Cut

/-! ## Deleting a cut occurrence raises the component count by exactly one -/

section Deletion

/-- Occurrences that do not cross `S` cannot carry a walk across `S`. -/
theorem mem_iff_of_reach_subEdges_local (G : CFGraph.{u}) (S : Finset G.V)
    (t : Multiset (G.V × G.V)) (ht : ∀ v : G.V, (v, v) ∉ t)
    (hNoCross : ∀ q ∈ t, (q.1 ∈ S ↔ q.2 ∈ S)) {x y : G.V}
    (hxy : Reach (subEdges G t ht) x y) : (x ∈ S ↔ y ∈ S) := by
  classical
  refine reach_propagate (H := subEdges G t ht)
    (motive := fun z ↦ (x ∈ S ↔ z ∈ S)) Iff.rfl ?_ hxy
  intro a b hab hA
  refine hA.trans ?_
  rw [num_edges_subEdges] at hab
  obtain ⟨q, hq⟩ := Multiset.card_pos_iff_exists_mem.1 hab
  rw [Multiset.mem_filter] at hq
  have hIff := hNoCross q hq.1
  rcases hq.2 with hEq | hEq
  · rw [hEq] at hIff
    exact hIff
  · rw [hEq] at hIff
    exact hIff.symm

/-- Deleting occurrences cannot create walks. -/
theorem reach_subEdges_local_mono (G : CFGraph.{u}) (p : G.V × G.V)
    (t : Multiset (G.V × G.V)) (hs : ∀ v : G.V, (v, v) ∉ p ::ₘ t)
    (ht : ∀ v : G.V, (v, v) ∉ t) {x y : G.V}
    (hxy : Reach (subEdges G t ht) x y) :
    Reach (subEdges G (p ::ₘ t) hs) x y := by
  refine reach_propagate (H := subEdges G t ht)
    (motive := fun z ↦ Reach (subEdges G (p ::ₘ t) hs) x z)
    (reach_refl _ _) ?_ hxy
  intro a b hab hA
  refine reach_trans hA (reach_single ?_)
  rw [num_edges_subEdges] at hab ⊢
  exact lt_of_lt_of_le hab
    (Multiset.card_le_card (Multiset.filter_le_filter _ (Multiset.le_cons_self _ _)))

/-- **Deleting a cut occurrence raises the component count by at least one.**
The cut set `S` is crossed by no surviving occurrence, so the two endpoints of
the deleted occurrence lie in different components afterwards.  The component
map of the smaller graph is injective into the larger one, and the classes of
the two endpoints supply one more class than its image accounts for.

This is the half that an Euler *identity* cannot supply: the opposite
inequality `componentCount_le_componentCount_cons_add_one` holds for an
arbitrary occurrence, but only a bridge is guaranteed to split a component. -/
theorem componentCount_cons_add_one_le (G : CFGraph.{u}) (S : Finset G.V)
    (p : G.V × G.V) (t : Multiset (G.V × G.V))
    (hs : ∀ v : G.V, (v, v) ∉ p ::ₘ t) (ht : ∀ v : G.V, (v, v) ∉ t)
    (hp1 : p.1 ∈ S) (hp2 : p.2 ∉ S)
    (hNoCross : ∀ q ∈ t, (q.1 ∈ S ↔ q.2 ∈ S)) :
    componentCount (subEdges G (p ::ₘ t) hs) + 1
      ≤ componentCount (subEdges G t ht) := by
  classical
  have hNotReach : ¬ Reach (subEdges G t ht) p.1 p.2 := fun h ↦
    hp2 ((mem_iff_of_reach_subEdges_local G S t ht hNoCross h).1 hp1)
  have hMono : ∀ x y : G.V, Reach (subEdges G t ht) x y →
      Reach (subEdges G (p ::ₘ t) hs) x y := fun _ _ h ↦
    reach_subEdges_local_mono G p t hs ht h
  have hPK : Reach (subEdges G (p ::ₘ t) hs) p.1 p.2 := by
    refine reach_single ?_
    rw [num_edges_subEdges]
    exact Multiset.card_pos_iff_exists_mem.2
      ⟨p, Multiset.mem_filter.2 ⟨Multiset.mem_cons_self _ _, Or.inl rfl⟩⟩
  set H := subEdges G t ht with hH
  set K := subEdges G (p ::ₘ t) hs with hK
  set A := Finset.univ.image (component K) with hA
  set B := Finset.univ.image (component H) with hB
  set f : Finset G.V → Finset G.V := fun c ↦ component H (repOf c) with hf
  -- the image of the `K`-classes under `f` sits inside the `H`-classes
  have hMaps : ∀ c ∈ A, f c ∈ B := fun c _ ↦
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hInjOn : Set.InjOn f ↑A := by
    intro c hc c' hc' hEq
    have hcRep : component K (repOf c) = c := component_repOf hc
    have hc'Rep : component K (repOf c') = c' := component_repOf hc'
    have hReachH : Reach H (repOf c) (repOf c') := by
      have hmem : repOf c' ∈ component H (repOf c) := by
        rw [show component H (repOf c) = component H (repOf c') from hEq]
        exact self_mem_component _
      exact (mem_component _ _).1 hmem
    rw [← hcRep, ← hc'Rep]
    exact component_eq_of_reach (hMono _ _ hReachH)
  -- neither endpoint class can be hit twice, so one of them is missed
  have hMissed : component H p.1 ∉ A.image f ∨ component H p.2 ∉ A.image f := by
    by_contra hBoth
    rw [not_or, not_not, not_not] at hBoth
    obtain ⟨c, hc, hcEq⟩ := Finset.mem_image.1 hBoth.1
    obtain ⟨c', hc', hc'Eq⟩ := Finset.mem_image.1 hBoth.2
    have hReach1 : Reach H p.1 (repOf c) := by
      refine (mem_component _ _).1 ?_
      rw [← hcEq]
      exact self_mem_component _
    have hReach2 : Reach H p.2 (repOf c') := by
      refine (mem_component _ _).1 ?_
      rw [← hc'Eq]
      exact self_mem_component _
    have hc1 : component K p.1 = c := by
      rw [component_eq_of_reach (hMono _ _ hReach1)]
      exact component_repOf hc
    have hc2 : component K p.2 = c' := by
      rw [component_eq_of_reach (hMono _ _ hReach2)]
      exact component_repOf hc'
    have hSame : c = c' := by
      rw [← hc1, ← hc2]
      exact component_eq_of_reach hPK
    have hEqComp : component H p.1 = component H p.2 := by
      rw [← hcEq, ← hc'Eq, hSame]
    have hMem : p.2 ∈ component H p.1 := by
      rw [hEqComp]
      exact self_mem_component _
    exact hNotReach ((mem_component _ _).1 hMem)
  -- count
  obtain ⟨z, hzB, hzNot⟩ :
      ∃ z : G.V, component H z ∈ B ∧ component H z ∉ A.image f := by
    rcases hMissed with h | h
    · exact ⟨p.1, Finset.mem_image_of_mem _ (Finset.mem_univ _), h⟩
    · exact ⟨p.2, Finset.mem_image_of_mem _ (Finset.mem_univ _), h⟩
  have hSubset : insert (component H z) (A.image f) ⊆ B := by
    refine Finset.insert_subset hzB ?_
    exact Finset.image_subset_iff.2 hMaps
  have hCard := Finset.card_le_card hSubset
  rw [Finset.card_insert_of_notMem hzNot, Finset.card_image_of_injOn hInjOn] at hCard
  unfold componentCount
  rw [← hA, ← hB]
  exact hCard

/-- **Deleting a cut occurrence raises the component count by exactly one.** -/
theorem componentCount_cons_eq (G : CFGraph.{u}) (p : G.V × G.V)
    (s : Multiset (G.V × G.V)) (hs' : ∀ v : G.V, (v, v) ∉ p ::ₘ s)
    (hs : ∀ v : G.V, (v, v) ∉ s) (hCut : IsCutOccurrence G p)
    (hLe : p ::ₘ s ≤ G.edges) :
    componentCount (subEdges G s hs)
      = componentCount (subEdges G (p ::ₘ s) hs') + 1 := by
  obtain ⟨S, hp1, hp2, hCross⟩ := hCut
  have hLower := componentCount_cons_add_one_le G S p s hs' hs hp1 hp2
    (noCross_of_isCutOccurrence G p S hCross s hLe)
  have hUpper := componentCount_le_componentCount_cons_add_one G p s hs' hs
  omega

/-- **Deleting a whole multiset of cut occurrences.**  Each deletion raises the
component count by exactly one, so the component count grows by the number of
deleted occurrences.  The cut hypothesis is stated for the ambient graph `G`
and is therefore inherited at every intermediate stage: a vertex set crossed by
only one occurrence of `G` is crossed by at most that one occurrence of any
submultiset. -/
theorem componentCount_subEdges_of_cut (G : CFGraph.{u})
    (d : Multiset (G.V × G.V)) :
    ∀ (s : Multiset (G.V × G.V)), s + d = G.edges →
      (∀ p ∈ d, IsCutOccurrence G p) →
      ∀ hs : ∀ v : G.V, (v, v) ∉ s,
        componentCount (subEdges G s hs)
          = componentCount G + Multiset.card d := by
  induction d using Multiset.induction_on with
  | empty =>
      intro s hEq _ hs
      have hsEq : s = G.edges := by simpa using hEq
      subst hsEq
      have hGraph : subEdges G G.edges hs = G := rfl
      rw [hGraph]
      simp
  | cons p d' ih =>
      intro s hEq hCut hs
      have hEq' : (p ::ₘ s) + d' = G.edges := by
        rw [Multiset.cons_add, ← Multiset.add_cons]
        exact hEq
      have hLe : p ::ₘ s ≤ G.edges :=
        Multiset.le_iff_exists_add.2 ⟨d', hEq'.symm⟩
      have hs' : ∀ v : G.V, (v, v) ∉ p ::ₘ s := fun v hv ↦
        G.loopless v (Multiset.mem_of_le hLe hv)
      have hIH := ih (p ::ₘ s) hEq'
        (fun q hq ↦ hCut q (Multiset.mem_cons_of_mem hq)) hs'
      have hStep := componentCount_cons_eq G p s hs' hs
        (hCut p (Multiset.mem_cons_self _ _)) hLe
      rw [hStep, hIH, Multiset.card_cons]
      omega

end Deletion

/-! ## The dangling occurrences of the quotient source are cut occurrences -/

section Dangling

variable {target : CFGraph} {degree : ℕ}

/-- The dangling occurrences of the quotient source, the complement of
`W4StableSource.nonDanglingEdges`. -/
noncomputable def danglingEdges (data : GluingDatum target degree) :
    Finset data.SourceEdge :=
  Finset.univ.filter fun edge ↦ IsDangling data edge

@[simp] theorem mem_danglingEdges (data : GluingDatum target degree)
    (edge : data.SourceEdge) :
    edge ∈ danglingEdges data ↔ IsDangling data edge := by
  unfold danglingEdges
  simp

/-- The surviving and the dangling occurrences partition all occurrences. -/
theorem nonDanglingEdges_val_add_danglingEdges_val
    (data : GluingDatum target degree) :
    (nonDanglingEdges data).val + (danglingEdges data).val
      = (Finset.univ : Finset data.SourceEdge).val := by
  unfold nonDanglingEdges danglingEdges
  rw [Finset.filter_val, Finset.filter_val, add_comm]
  exact Multiset.filter_add_not _ _

/-- The occurrences of the pruned source together with the endpoint pairs of
the dangling occurrences are the occurrences of the quotient source. -/
theorem prunedSource_edges_add_dangling (data : GluingDatum target degree) :
    (prunedSource data).edges
        + (danglingEdges data).val.map data.sourceEnds
      = data.sourceGraph.edges := by
  show (nonDanglingEdges data).val.map data.sourceEnds
      + (danglingEdges data).val.map data.sourceEnds
    = (Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds
  rw [← Multiset.map_add, nonDanglingEdges_val_add_danglingEdges_val]

/-- **A dangling occurrence is a cut occurrence.**  Its `DanglingSide`
certificate carries a `Utilities.SeparatingEdgeCut`, whose `cross_num_edges`
field says precisely that the distinguished occurrence is the only one running
between the side and its complement.  The second orientation of the
certificate is read through the complementary vertex set. -/
theorem isCutOccurrence_of_isDangling (data : GluingDatum target degree)
    {edge : data.SourceEdge} (hDangling : IsDangling data edge) :
    IsCutOccurrence data.sourceGraph (data.sourceEnds edge) := by
  classical
  rcases hDangling with hSide | hSide
  · obtain ⟨cut⟩ := hSide
    exact ⟨cut.side, cut.left_mem, cut.right_not_mem, cut.cross_num_edges⟩
  · obtain ⟨cut⟩ := hSide
    refine ⟨Finset.univ \ cut.side, ?_, ?_, ?_⟩
    · exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, cut.right_not_mem⟩
    · simp [Finset.mem_sdiff, cut.left_mem]
    · intro a b ha hb
      have ha' : a ∉ cut.side := (Finset.mem_sdiff.1 ha).2
      have hb' : b ∈ cut.side := by
        by_contra hbb
        exact hb (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hbb⟩)
      rw [num_edges_symmetric, cut.cross_num_edges b a hb' ha']
      by_cases hCase : a = (data.sourceEnds edge).1 ∧ b = (data.sourceEnds edge).2
      · rw [ite_eq_left hCase, ite_eq_left ⟨hCase.2, hCase.1⟩]
      · rw [ite_eq_right hCase, ite_eq_right fun h ↦ hCase ⟨h.2, h.1⟩]

end Dangling

/-! ## The first Betti number is unchanged -/

section Main

variable {target : CFGraph} {degree : ℕ}

/-- Every endpoint pair coming from a dangling occurrence is a cut occurrence
of the quotient source. -/
theorem isCutOccurrence_of_mem_dangling (data : GluingDatum target degree)
    (p : data.SourceVertex × data.SourceVertex)
    (hp : p ∈ (danglingEdges data).val.map data.sourceEnds) :
    IsCutOccurrence data.sourceGraph p := by
  obtain ⟨edge, hEdge, hp⟩ := Multiset.mem_map.1 hp
  subst hp
  exact isCutOccurrence_of_isDangling data
    ((mem_danglingEdges data edge).1 hEdge)

/-- **The pruned source has one component per deleted dangling occurrence,
plus one.**  The quotient source is connected, and every dangling deletion is
a bridge deletion. -/
theorem componentCount_prunedSource (data : GluingDatum target degree)
    (hConnected : data.Connected) :
    componentCount (prunedSource data) = 1 + (danglingEdges data).card := by
  have hLoopless : ∀ v : data.sourceGraph.V, (v, v) ∉ (prunedSource data).edges :=
    (prunedSource data).loopless
  have hGraph : subEdges data.sourceGraph (prunedSource data).edges hLoopless
      = prunedSource data := rfl
  have hCount := componentCount_subEdges_of_cut data.sourceGraph
    ((danglingEdges data).val.map data.sourceEnds) (prunedSource data).edges
    (prunedSource_edges_add_dangling data) (isCutOccurrence_of_mem_dangling data)
    hLoopless
  rw [hGraph, (componentCount_eq_one_iff data.sourceGraph).2 hConnected] at hCount
  rw [hCount]
  exact congrArg (fun k ↦ 1 + k) (Multiset.card_map _ _)

/-- **Deleting the dangling occurrences does not change the first Betti
number.**  The deliverable: with `b₁ = cyclomatic` on the pruned source and
`genus = |E| - |V| + 1` on the connected quotient source, the two agree.

Each dangling deletion drops the occurrence count by one and raises the
component count by one, so `|E| - |V| + c` is unchanged; and on the connected
quotient source `cyclomatic` is `genus`.

The only hypothesis is connectedness of the quotient source, which is the
first component of `GluingDatum.Valid`. -/
theorem cyclomatic_prunedSource_eq_genus_sourceGraph
    (data : GluingDatum target degree) (hConnected : data.Connected) :
    cyclomatic (prunedSource data) = genus data.sourceGraph := by
  have hCard : Multiset.card (prunedSource data).edges
      + Multiset.card ((danglingEdges data).val.map data.sourceEnds)
      = Multiset.card data.sourceGraph.edges := by
    rw [← Multiset.card_add]
    exact congrArg Multiset.card (prunedSource_edges_add_dangling data)
  have hMapCard : Multiset.card ((danglingEdges data).val.map data.sourceEnds)
      = (danglingEdges data).card := Multiset.card_map _ _
  have hVertices : Fintype.card (prunedSource data).V
      = Fintype.card data.sourceGraph.V := rfl
  have hComponents := componentCount_prunedSource data hConnected
  unfold cyclomatic genus
  omega

/-- The same identity read off `GluingDatum.Valid`, whose first component is
the connectedness of the quotient source. -/
theorem cyclomatic_prunedSource_eq_genus_sourceGraph_of_valid
    (data : GluingDatum target degree) (hValid : data.Valid) :
    cyclomatic (prunedSource data) = genus data.sourceGraph :=
  cyclomatic_prunedSource_eq_genus_sourceGraph data hValid.1

/-- The occurrence count of the pruned source in terms of the genus of the
quotient source and its component count, the form an Euler count consumes. -/
theorem card_nonDanglingEdges_eq (data : GluingDatum target degree)
    (hConnected : data.Connected) :
    ((nonDanglingEdges data).card : ℤ)
      = genus data.sourceGraph + (Fintype.card data.SourceVertex : ℤ)
          - (componentCount (prunedSource data) : ℤ) := by
  have hCyc := cyclomatic_prunedSource_eq_genus_sourceGraph data hConnected
  rw [cyclomatic_prunedSource] at hCyc
  omega

end Main

end DraismaVargas.LocalCases.DanglingBetti
