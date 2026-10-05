module

public import DraismaVargas.LocalCases.TerminalContraction
public import DraismaVargas.LocalCases.NonDanglingValency

@[expose] public section

/-!
# The structure of a dangling side

Two facts about the objects of `LocalCases/PrunedContractedSpec.lean` (the
separation of pendant classes, and the class/slot count) rest on one structural
fact:

> the far side of a dangling occurrence is a pendant tree, all of whose
> vertices have non-dangling valency zero, and whose contraction classes never
> escape it.

This module proves exactly that, about `W4StableSource.DanglingSide` alone.  It
mentions neither `ClearedFace.SourceContractionTopology` nor `prunedSpec`;
`LocalCases/PrunedContractedSpecResidues.lean` is what turns these statements
into `PendantSeparated` and the class/slot count.

## The three theorems

* `nonDanglingValency_eq_zero_of_mem_side` — **every** occurrence incident to
  **any** vertex of a dangling side is itself dangling.  The proof is a strong
  induction on the cardinality of the side.  At the inner endpoint the descent
  step `DanglingDescent.exists_danglingSide_of_mem_side` does the work
  directly; away from it, `exists_smaller_side` produces the branch of the
  tree that the vertex sits in, which is a strictly smaller dangling side
  containing it, and the induction hypothesis applies there.

* `mem_side_of_reachIn` — a chain of **zero-length** occurrences starting
  inside the side stays inside it, provided the cut occurrence itself has
  positive length.  The only occurrence crossing the cut is the cut
  occurrence, and it is positive, so no zero chain can use it.  This is the
  "classes cannot escape" half: `DegSpec.rep`-equality on the canonical
  quotient-source core is exactly `ReachIn core sourceZeroSet`
  (`ContractionForestCensusGeneral.compFold_iff`, through
  `TerminalContraction.sourceDegSpec_rep`).

* `inner_eq_of_danglingData` — as soon as **one** source vertex survives
  pruning, a dangling occurrence has only one dangling orientation, so "the
  far side" is well defined.  Its engine is `mem_side_union`: two dangling
  cuts each of whose outer endpoints lies in the other's side cover the whole
  vertex set, and then no vertex survives at all.

## Walks

The walks are `DanglingDescent.Reach` refined by a predicate on the vertex
each step lands on (`ReachP`).  That refinement is what lets a walk be
confined: `mem_side_of_reachP` says a walk that starts inside a dangling side
and never steps onto its outer endpoint stays inside the side, which is the
single geometric fact used three times below.
-/

namespace DraismaVargas.LocalCases.DanglingSideStructure

open Utilities.Certificate
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.LocalCases.TerminalContraction
open Utilities.Certificate.ContractionForestCensusGeneral

universe u

/-! ## 1.  Walks that avoid a vertex -/

section Walks

variable {G : CFGraph.{u}}

/-- Reachability by steps each of which lands on a vertex satisfying `P`. -/
def ReachP (G : CFGraph.{u}) (P : G.V → Prop) : G.V → G.V → Prop :=
  Relation.ReflTransGen fun a b ↦ 0 < num_edges G a b ∧ P b

theorem reachP_refl (P : G.V → Prop) (a : G.V) : ReachP G P a a :=
  Relation.ReflTransGen.refl

theorem reachP_tail {P : G.V → Prop} {a b c : G.V} (h : ReachP G P a b)
    (hbc : 0 < num_edges G b c) (hc : P c) : ReachP G P a c :=
  Relation.ReflTransGen.tail h ⟨hbc, hc⟩

/-- Weakening the predicate weakens the walk. -/
theorem reachP_mono {P Q : G.V → Prop} (hPQ : ∀ z : G.V, P z → Q z) {a b : G.V}
    (h : ReachP G P a b) : ReachP G Q a b :=
  Relation.ReflTransGen.mono (fun _ y hxy ↦ ⟨hxy.1, hPQ y hxy.2⟩) a b h

/-- **A confined walk leaving a vertex set crosses it**, at a step whose far
end still satisfies the predicate. -/
theorem exists_cross_of_reachP {P : G.V → Prop} (T : Finset G.V) {x y : G.V}
    (h : ReachP G P x y) (hx : x ∈ T) :
    y ∉ T → ∃ p ∈ T, ∃ q ∉ T, 0 < num_edges G p q ∧ P q := by
  induction h with
  | refl => intro hy; exact absurd hx hy
  | @tail b c _ hbc ih =>
      intro hc
      by_cases hb : b ∈ T
      · exact ⟨b, hb, c, hc, hbc.1, hbc.2⟩
      · exact ih hb

/-- **The first step of a nontrivial walk**, together with the rest of the
walk made to avoid the starting vertex. -/
theorem exists_first_step {x y : G.V} (h : Reach G x y) :
    y ≠ x → ∃ w : G.V, 0 < num_edges G x w ∧ ReachP G (fun z ↦ z ≠ x) w y := by
  induction h with
  | refl => intro hne; exact absurd rfl hne
  | @tail b c _ hbc ih =>
      intro hcx
      by_cases hb : b = x
      · subst hb
        exact ⟨c, hbc, reachP_refl _ _⟩
      · obtain ⟨w, hw, hreach⟩ := ih hb
        exact ⟨w, hw, reachP_tail hreach hbc hcx⟩

/-- A walk inside an induced subgraph is a walk of the ambient graph confined
to the inducing set. -/
theorem reachP_of_reach_induced {S : Finset G.V} (hS : S.Nonempty)
    {a b : (Utilities.inducedSubgraph G S hS).V}
    (h : Reach (Utilities.inducedSubgraph G S hS) a b) :
    ReachP G (fun z ↦ z ∈ S) a.1 b.1 := by
  induction h with
  | refl => exact reachP_refl _ _
  | @tail p q _ hpq ih =>
      refine reachP_tail ih ?_ q.2
      have hEq := Utilities.num_edges_inducedSubgraph G S hS p q
      omega

/-- A confined walk inside an induced subgraph is a confined walk of the
ambient graph. -/
theorem reachP_of_reachP_induced {S : Finset G.V} (hS : S.Nonempty)
    {P : G.V → Prop} {a b : (Utilities.inducedSubgraph G S hS).V}
    (h : ReachP (Utilities.inducedSubgraph G S hS) (fun z ↦ P z.1) a b) :
    ReachP G P a.1 b.1 := by
  induction h with
  | refl => exact reachP_refl _ _
  | @tail p q _ hpq ih =>
      refine reachP_tail ih ?_ hpq.2
      have hEq := Utilities.num_edges_inducedSubgraph G S hS p q
      have hpq' := hpq.1
      omega

end Walks

/-! ## 2.  A dangling side confines the walks that avoid its outer endpoint -/

section Confinement

variable {G : CFGraph.{u}}

/-- **Confinement.**  A walk that starts on a dangling side and never steps
onto the cut's outer endpoint never leaves the side: the only occurrence
crossing the cut ends at that outer endpoint. -/
theorem mem_side_of_reachP {inner outer : G.V} (cut : DanglingSide G inner outer)
    {x y : G.V} (hx : x ∈ cut.side)
    (h : ReachP G (fun z ↦ z ≠ outer) x y) : y ∈ cut.side := by
  by_contra hy
  obtain ⟨p, hp, q, hq, hpq, hqne⟩ := exists_cross_of_reachP cut.side h hx hy
  have hCross := cut.cross_num_edges p q hp hq
  by_cases hPair : p = inner ∧ q = outer
  · exact hqne hPair.2
  · rw [ite_eq_right hPair] at hCross
    omega

/-- **The branch of a tree.**  A vertex of a dangling side other than its
inner endpoint lies on a strictly smaller dangling side, cut off by the first
occurrence of a walk to it from the inner endpoint. -/
theorem exists_smaller_side {inner outer : G.V} (cut : DanglingSide G inner outer)
    {v : G.V} (hv : v ∈ cut.side) (hne : v ≠ inner) :
    ∃ (w : G.V) (smaller : DanglingSide G w inner),
      smaller.side.card < cut.side.card ∧ v ∈ smaller.side := by
  classical
  have hSne : cut.side.Nonempty := ⟨inner, cut.left_mem⟩
  have hReach : Reach (Utilities.inducedSubgraph G cut.side hSne)
      ⟨inner, cut.left_mem⟩ ⟨v, hv⟩ :=
    reach_of_graph_connected cut.side_connected _ _
  obtain ⟨iw, hEdgeH, hWalk⟩ := exists_first_step hReach (by
    intro hEq
    exact hne (congrArg Subtype.val hEq))
  have hEdgeG : 0 < num_edges G inner iw.1 := by
    have hEq : num_edges (Utilities.inducedSubgraph G cut.side hSne)
        ⟨inner, cut.left_mem⟩ iw = num_edges G inner iw.1 :=
      Utilities.num_edges_inducedSubgraph G cut.side hSne ⟨inner, cut.left_mem⟩ iw
    omega
  obtain ⟨smaller, hLess⟩ := exists_danglingSide_of_mem_side cut iw.2 hEdgeG
  refine ⟨iw.1, smaller, hLess, ?_⟩
  refine mem_side_of_reachP smaller smaller.left_mem
    (reachP_of_reachP_induced (P := fun z ↦ z ≠ inner) (a := iw)
      (b := ⟨v, hv⟩) hSne ?_)
  refine reachP_mono (fun z hz ↦ ?_) hWalk
  intro hEq
  exact hz (Subtype.ext hEq)

/-- **Two dangling cuts that face each other cover everything.**  If the outer
endpoint of each cut lies on the side of the other, then every vertex lies on
one of the two sides. -/
theorem mem_side_union {x₁ y₁ x₂ y₂ : G.V}
    (cut₁ : DanglingSide G x₁ y₁) (cut₂ : DanglingSide G x₂ y₂)
    (h₁ : y₁ ∈ cut₂.side) (h₂ : y₂ ∈ cut₁.side) (z : G.V) :
    z ∈ cut₁.side ∨ z ∈ cut₂.side := by
  classical
  by_cases hz : z ∈ cut₁.side
  · exact Or.inl hz
  refine Or.inr ?_
  have hy₁ : y₁ ∈ Finset.univ \ cut₁.side :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, cut₁.right_not_mem⟩
  have hzc : z ∈ Finset.univ \ cut₁.side :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩
  have hSne : (Finset.univ \ cut₁.side).Nonempty := ⟨y₁, hy₁⟩
  have hReach : Reach (Utilities.inducedSubgraph G (Finset.univ \ cut₁.side) hSne)
      ⟨y₁, hy₁⟩ ⟨z, hzc⟩ :=
    reach_of_graph_connected cut₁.complement_connected _ _
  refine mem_side_of_reachP cut₂ h₁ ?_
  refine reachP_mono (fun w hw ↦ ?_) (reachP_of_reach_induced hSne hReach)
  intro hEq
  exact (Finset.mem_sdiff.mp hw).2 (hEq ▸ h₂)

/-- Forgetting the confinement. -/
theorem reach_of_reachP {P : G.V → Prop} {a b : G.V} (h : ReachP G P a b) :
    Reach G a b :=
  Relation.ReflTransGen.mono (fun _ _ hxy ↦ hxy.1) a b h

/-- **A dangling cut forces the ambient graph connected**: both sides are
connected and the cut occurrence joins them.  Contrapositively, a disconnected
quotient source has no dangling occurrence at all — which is why the class/slot
count of `PrunedContractedSpecResidues` needs source connectivity and not
merely a nonempty set of kept classes. -/
theorem graph_connected_of_danglingSide {x y : G.V} (cut : DanglingSide G x y) :
    graph_connected G := by
  classical
  have hSne : cut.side.Nonempty := ⟨x, cut.left_mem⟩
  have hy : y ∈ Finset.univ \ cut.side :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, cut.right_not_mem⟩
  have hCne : (Finset.univ \ cut.side).Nonempty := ⟨y, hy⟩
  have hxy : Reach G x y := by
    refine reach_single ?_
    have hOne := cut.num_edges_endpoints
    omega
  refine graph_connected_of_reach x ?_
  intro z
  by_cases hz : z ∈ cut.side
  · exact reach_of_reachP (reachP_of_reach_induced hSne
      (reach_of_graph_connected cut.side_connected ⟨x, cut.left_mem⟩ ⟨z, hz⟩))
  · exact reach_trans hxy (reach_of_reachP (reachP_of_reach_induced hCne
      (reach_of_graph_connected cut.complement_connected ⟨y, hy⟩
        ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩⟩)))

end Confinement

/-! ## 3.  Every occurrence inside a dangling side is dangling -/

section Datum

variable {target : CFGraph} {degree : ℕ}

/-- **The structure theorem, first half.**  Every source occurrence incident to
a vertex of a dangling side is itself dangling.  Strong induction on the size
of the side: at the inner endpoint the descent step applies directly, and any
other vertex of the side lies on a strictly smaller dangling side. -/
theorem isDangling_of_incident_mem_side (data : GluingDatum target degree) :
    ∀ (size : ℕ) (inner outer : data.SourceVertex)
      (cut : DanglingSide data.sourceGraph inner outer), cut.side.card = size →
      ∀ vertex ∈ cut.side, ∀ edge : data.SourceEdge,
        Incident data edge vertex → IsDangling data edge := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
    intro inner outer cut hCard vertex hVertex edge hIncident
    by_cases hv : vertex = inner
    · subst hv
      obtain ⟨other, hEnds⟩ := exists_other_sourceEnd data hIncident
      have hPos : 0 < num_edges data.sourceGraph vertex other :=
        num_edges_pos_of_sourceEnds data hEnds
      by_cases hOther : other ∈ cut.side
      · obtain ⟨smaller, _⟩ := exists_danglingSide_of_mem_side cut hOther hPos
        exact isDangling_of_danglingSide data hEnds.symm smaller
      · have hCross := cut.cross_num_edges vertex other hVertex hOther
        have hOuter : other = outer := by
          by_contra hne
          rw [ite_eq_right (fun hPair ↦ hne hPair.2)] at hCross
          omega
        subst hOuter
        exact isDangling_of_danglingSide data hEnds cut
    · obtain ⟨w, smaller, hLess, hMem⟩ := exists_smaller_side cut hVertex hv
      exact ih smaller.side.card (hCard ▸ hLess) w inner smaller rfl vertex hMem
        edge hIncident

/-- Vanishing non-dangling valency is exactly "every incident occurrence
dangles". -/
theorem nonDanglingValency_eq_zero_iff (data : GluingDatum target degree)
    (vertex : data.SourceVertex) :
    nonDanglingValency data vertex = 0 ↔
      ∀ edge : data.SourceEdge, Incident data edge vertex → IsDangling data edge := by
  classical
  constructor
  · intro hZero edge hIncident
    by_contra hNot
    have hPos : 0 < nonDanglingValency data vertex := by
      refine Finset.card_pos.mpr ⟨edge, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hNot, hIncident⟩
    omega
  · intro hAll
    by_contra hNe
    obtain ⟨edge, hMem⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hNe)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hMem
    exact hMem.1 (hAll edge hMem.2)

/-- **The structure theorem, first half, as a valency statement.**  Every
vertex of a dangling side has non-dangling valency zero: nothing on a pendant
tree survives pruning. -/
theorem nonDanglingValency_eq_zero_of_mem_side (data : GluingDatum target degree)
    {inner outer : data.SourceVertex}
    (cut : DanglingSide data.sourceGraph inner outer)
    {vertex : data.SourceVertex} (hVertex : vertex ∈ cut.side) :
    nonDanglingValency data vertex = 0 :=
  (nonDanglingValency_eq_zero_iff data vertex).mpr fun edge hIncident ↦
    isDangling_of_incident_mem_side data cut.side.card inner outer cut rfl vertex
      hVertex edge hIncident

/-- **Nothing dangles in a disconnected quotient source.** -/
theorem not_isDangling_of_not_graph_connected (data : GluingDatum target degree)
    (hDisconnected : ¬ graph_connected data.sourceGraph)
    (edge : data.SourceEdge) : ¬ IsDangling data edge := by
  rintro (hCut | hCut) <;> obtain ⟨cut⟩ := hCut <;>
    exact hDisconnected (graph_connected_of_danglingSide cut)

/-! ## 4.  The chosen far side of a dangling occurrence -/

/-- A dangling occurrence, oriented: the inner endpoint, the outer endpoint,
and the genus-zero cut between them. -/
structure DanglingData (data : GluingDatum target degree)
    (edge : data.SourceEdge) where
  /-- The endpoint on the pendant side. -/
  inner : data.SourceVertex
  /-- The endpoint the pendant side hangs from. -/
  outer : data.SourceVertex
  /-- They are the two ends of the occurrence, in one order or the other. -/
  ends : data.sourceEnds edge = (inner, outer) ∨
    data.sourceEnds edge = (outer, inner)
  /-- The cut itself. -/
  cut : DanglingSide data.sourceGraph inner outer

/-- An oriented dangling occurrence is dangling. -/
theorem isDangling_of_danglingData {data : GluingDatum target degree}
    {edge : data.SourceEdge} (item : DanglingData data edge) :
    IsDangling data edge :=
  isDangling_of_danglingSide data item.ends item.cut

/-- and conversely. -/
theorem nonempty_danglingData {data : GluingDatum target degree}
    {edge : data.SourceEdge} (hDangling : IsDangling data edge) :
    Nonempty (DanglingData data edge) := by
  rcases hDangling with hCut | hCut
  · obtain ⟨cut⟩ := hCut
    exact ⟨{ inner := (data.sourceEnds edge).1
             outer := (data.sourceEnds edge).2
             ends := Or.inl rfl
             cut := cut }⟩
  · obtain ⟨cut⟩ := hCut
    exact ⟨{ inner := (data.sourceEnds edge).2
             outer := (data.sourceEnds edge).1
             ends := Or.inr rfl
             cut := cut }⟩

/-- **The far side of a dangling occurrence**, chosen once and for all.
`inner_eq_of_danglingData` shows the choice is forced as soon as one vertex
survives pruning. -/
noncomputable def chosenDangling {data : GluingDatum target degree}
    {edge : data.SourceEdge} (hDangling : IsDangling data edge) :
    DanglingData data edge :=
  Classical.choice (nonempty_danglingData hDangling)

/-- Two dangling cuts facing each other leave no surviving vertex at all. -/
theorem false_of_mem_side_union (data : GluingDatum target degree)
    {survivor : data.SourceVertex} (hSurvivor : 0 < nonDanglingValency data survivor)
    {x₁ y₁ x₂ y₂ : data.SourceVertex}
    (cut₁ : DanglingSide data.sourceGraph x₁ y₁)
    (cut₂ : DanglingSide data.sourceGraph x₂ y₂)
    (h₁ : y₁ ∈ cut₂.side) (h₂ : y₂ ∈ cut₁.side) : False := by
  rcases mem_side_union cut₁ cut₂ h₁ h₂ survivor with hMem | hMem
  · rw [nonDanglingValency_eq_zero_of_mem_side data cut₁ hMem] at hSurvivor
    omega
  · rw [nonDanglingValency_eq_zero_of_mem_side data cut₂ hMem] at hSurvivor
    omega

/-- **The orientation is forced.**  As soon as one source vertex survives
pruning, a dangling occurrence has exactly one dangling orientation, so "the
far side" and "the inner endpoint" are well defined. -/
theorem inner_eq_of_danglingData (data : GluingDatum target degree)
    {survivor : data.SourceVertex} (hSurvivor : 0 < nonDanglingValency data survivor)
    {edge : data.SourceEdge} (first second : DanglingData data edge) :
    first.inner = second.inner := by
  rcases first.ends with hFirst | hFirst <;> rcases second.ends with hSecond | hSecond
  · rw [hFirst] at hSecond
    exact congrArg Prod.fst hSecond
  · rw [hFirst] at hSecond
    have hOne : first.inner = second.outer := congrArg Prod.fst hSecond
    have hTwo : first.outer = second.inner := congrArg Prod.snd hSecond
    refine (false_of_mem_side_union data hSurvivor first.cut second.cut ?_ ?_).elim
    · rw [hTwo]
      exact second.cut.left_mem
    · rw [← hOne]
      exact first.cut.left_mem
  · rw [hFirst] at hSecond
    have hOne : first.outer = second.inner := congrArg Prod.fst hSecond
    have hTwo : first.inner = second.outer := congrArg Prod.snd hSecond
    refine (false_of_mem_side_union data hSurvivor first.cut second.cut ?_ ?_).elim
    · rw [hOne]
      exact second.cut.left_mem
    · rw [← hTwo]
      exact first.cut.left_mem
  · rw [hFirst] at hSecond
    exact congrArg Prod.snd hSecond

/-- **Two dangling occurrences whose inner endpoints lie on each other's
sides.**  The outer endpoint of the second lies on the first's side too,
unless the two occurrences coincide: the only occurrence crossing the first
cut is its own. -/
theorem outer_mem_side_of_inner_mem_side (data : GluingDatum target degree)
    {edge₁ edge₂ : data.SourceEdge} (item₁ : DanglingData data edge₁)
    (item₂ : DanglingData data edge₂) (hNe : edge₂ ≠ edge₁)
    (hMem : item₂.inner ∈ item₁.cut.side) : item₂.outer ∈ item₁.cut.side := by
  by_contra hOut
  have hCross := item₁.cut.cross_num_edges item₂.inner item₂.outer hMem hOut
  have hPos : 0 < num_edges data.sourceGraph item₂.inner item₂.outer :=
    num_edges_pos_of_sourceEnds data item₂.ends
  have hPair : item₂.inner = item₁.inner ∧ item₂.outer = item₁.outer := by
    by_contra hno
    have hVanish : num_edges data.sourceGraph item₂.inner item₂.outer = 0 := by
      rw [hCross]
      exact ite_eq_right hno
    omega
  have hOne : num_edges data.sourceGraph item₂.inner item₂.outer = 1 := by
    rw [hCross]
    exact ite_eq_left hPair
  have hEnds : data.sourceEnds edge₂ = (item₁.inner, item₁.outer) ∨
      data.sourceEnds edge₂ = (item₁.outer, item₁.inner) := by
    rw [← hPair.1, ← hPair.2]
    exact item₂.ends
  have hTwo := two_le_num_edges_of_ne data hNe hEnds item₁.ends
  rw [hPair.1, hPair.2] at hOne
  omega

/-- **Distinct dangling occurrences have distinct far classes.**  If the inner
endpoint of each of two distinct dangling occurrences lies on the other's far
side, then nothing survives pruning. -/
theorem false_of_inner_mem_side (data : GluingDatum target degree)
    {survivor : data.SourceVertex} (hSurvivor : 0 < nonDanglingValency data survivor)
    {edge₁ edge₂ : data.SourceEdge} (item₁ : DanglingData data edge₁)
    (item₂ : DanglingData data edge₂) (hNe : edge₁ ≠ edge₂)
    (hMem₂ : item₂.inner ∈ item₁.cut.side) (hMem₁ : item₁.inner ∈ item₂.cut.side) :
    False :=
  false_of_mem_side_union data hSurvivor item₁.cut item₂.cut
    (outer_mem_side_of_inner_mem_side data item₂ item₁ hNe hMem₁)
    (outer_mem_side_of_inner_mem_side data item₁ item₂ (Ne.symm hNe) hMem₂)

/-- `inner_eq_of_danglingData`, transported along an equality of occurrences. -/
theorem inner_eq_of_danglingData_of_eq (data : GluingDatum target degree)
    {survivor : data.SourceVertex} (hSurvivor : 0 < nonDanglingValency data survivor)
    {edge₁ edge₂ : data.SourceEdge} (hEq : edge₁ = edge₂)
    (item₁ : DanglingData data edge₁) (item₂ : DanglingData data edge₂) :
    item₁.inner = item₂.inner := by
  subst hEq
  exact inner_eq_of_danglingData data hSurvivor item₁ item₂

end Datum

/-! ## 5.  Zero-length chains never leave the side -/

section Zero

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- One zero-length occurrence out of a dangling side whose cut occurrence is
positive stays inside the side. -/
theorem mem_side_of_sourceLength_zero
    (realization : data.NonnegativeIntegralRealization)
    {inner outer : data.SourceVertex}
    (cut : DanglingSide data.sourceGraph inner outer)
    {edge : data.SourceEdge}
    (hEnds : data.sourceEnds edge = (inner, outer) ∨
      data.sourceEnds edge = (outer, inner))
    (hPos : 0 < realization.sourceLength edge)
    {zero : data.SourceEdge} (hZero : realization.sourceLength zero = 0)
    {p q : data.SourceVertex}
    (hPair : data.sourceEnds zero = (p, q) ∨ data.sourceEnds zero = (q, p))
    (hp : p ∈ cut.side) : q ∈ cut.side := by
  by_contra hq
  have hCross := cut.cross_num_edges p q hp hq
  have hPosPair : 0 < num_edges data.sourceGraph p q :=
    num_edges_pos_of_sourceEnds data hPair
  have hEq : p = inner ∧ q = outer := by
    by_contra hne
    have hVanish : num_edges data.sourceGraph p q = 0 := by
      rw [hCross]
      exact ite_eq_right hne
    omega
  have hOne : num_edges data.sourceGraph p q = 1 := by
    rw [hCross]
    exact ite_eq_left hEq
  have hZeroEnds : data.sourceEnds zero = (inner, outer) ∨
      data.sourceEnds zero = (outer, inner) := by
    rw [← hEq.1, ← hEq.2]
    exact hPair
  have hNe : zero ≠ edge := by
    intro hEqual
    rw [hEqual] at hZero
    omega
  have hTwo := two_le_num_edges_of_ne data hNe hZeroEnds hEnds
  rw [hEq.1, hEq.2] at hOne
  omega

/-- **The structure theorem, second half.**  A chain of zero-length
occurrences starting on a dangling side whose cut occurrence has positive
length never leaves the side.  `ReachIn core sourceZeroSet` is exactly
`DegSpec.rep`-equality on the canonical quotient-source core, so this says the
contraction classes of the side's vertices contain no vertex outside it. -/
theorem mem_side_of_reachIn (realization : data.NonnegativeIntegralRealization)
    {inner outer : data.SourceVertex}
    (cut : DanglingSide data.sourceGraph inner outer)
    {edge : data.SourceEdge}
    (hEnds : data.sourceEnds edge = (inner, outer) ∨
      data.sourceEnds edge = (outer, inner))
    (hPos : 0 < realization.sourceLength edge)
    {a b : Fin (Fintype.card data.sourceGraph.V)}
    (ha : (vertexIndex data).symm a ∈ cut.side)
    (hReach : ReachIn (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet a b) :
    (vertexIndex data).symm b ∈ cut.side := by
  induction hReach with
  | refl => exact ha
  | @tail p q _ hpq ih =>
      obtain ⟨slot, hSlot, hCase⟩ := hpq
      rw [mem_edgeList] at hSlot
      have hZero : realization.sourceLength (realization.sourceEdgeAt slot) = 0 :=
        (GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet
          realization slot).mp hSlot
      have hTail : (vertexIndex data).symm
          ((UnitSubdivisionPresentation.core data.sourceGraph).tail slot) =
          (data.sourceEnds (realization.sourceEdgeAt slot)).1 := by
        rw [core_tail_eq realization slot]
        exact (vertexIndex data).symm_apply_apply _
      have hHead : (vertexIndex data).symm
          ((UnitSubdivisionPresentation.core data.sourceGraph).head slot) =
          (data.sourceEnds (realization.sourceEdgeAt slot)).2 := by
        rw [core_head_eq realization slot]
        exact (vertexIndex data).symm_apply_apply _
      rcases hCase with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · refine mem_side_of_sourceLength_zero realization cut hEnds hPos hZero
          (p := (vertexIndex data).symm p) (q := (vertexIndex data).symm q)
          (Or.inl ?_) ih
        rw [← hp, ← hq, hTail, hHead]
      · refine mem_side_of_sourceLength_zero realization cut hEnds hPos hZero
          (p := (vertexIndex data).symm p) (q := (vertexIndex data).symm q)
          (Or.inr ?_) ih
        rw [← hp, ← hq, hTail, hHead]

end Zero

end DraismaVargas.LocalCases.DanglingSideStructure
