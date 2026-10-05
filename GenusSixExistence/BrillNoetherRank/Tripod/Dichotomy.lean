module

public import GenusSixExistence.BrillNoetherRank.Tripod.ClawDefs
public import DraismaVargasCount.LeafFibre
public import DraismaVargas.LocalCases.LeafFacetNoReturn
public import Utilities.Foundations.PendantDeletion
public import DraismaVargasCount.RowGeodesic
public import Utilities.IntegralGeometry.DeterminantExpansion

@[expose] public section

/-!
# The dichotomy over the tripod gadget, glued if and only if not a claw

The proof of `Classification.dichotomy`. Prose proof: `Research/genus-six-brill-noether-rank.md`,
§4.3 (The shape of a leg), §4.4 (The lost-edge bound, and the column trick), §4.5 (Long legs leave
the image of G), §4.6 (Claw versus glued) and §4.8 (The parameter count); section and statement
numbers in this file refer to that note, and "section N below" to the sections of this file.

Throughout, `κ` is a frame of the gadget `Γ̃ = tripodCore core s`: a full-dimensional gluing
datum over a target tree `T` with its stable graph identified with `Γ̃`. A target edge is
**lost** (`IsLost`) when no non-dangling source edge of a G-slot lies over it (§4.1, the
set `L = E(T) ∖ E(T̂)`).

## The two directions

* **claw ⇒ not glued** (`not_isGlued_of_isClaw`, at every degree and with no hypothesis on
  the core or the request). If every leg left its mark up a leaf edge `h_k`, the
  three `h_k` would be distinct lost edges (Lemma 4.4: all survivors over a leaf edge lie on one
  stable path, `LeafFibre.stablePath_eq_of_mem_leafSurvivors`), and an edge of `T` at
  `φ(c) ∉ φ(G)` would be a fourth: it is lost because `φ(c) ∉ φ(G)`, and it is none of the `h_k`
  because the ends of `h_k` are `φ(k) ∈ φ(G)` and a leaf, while `φ(c)`, under a branch vertex,
  is not a leaf. Four lost edges contradict Lemma 4.5.
* **not claw ⇒ glued** (`isGlued_of_not_isClaw`, for connected `G̃`). If `φ(c) ∈ φ(G)`, every
  leg has a leaf detour (Theorem 4.7(a): Lemma 4.2(i), the subtree `T̂`, and the length bound
  Lemma 4.6 at long legs); the three detour leaf edges are distinct and lost (Lemma 4.4), hence
  all the lost edges (Lemma 4.5); and then each detour is at the leg's own mark
  (Proposition 4.11, §4.8; section 6 below).

**How `T̂` is a subtree** (section 5 below). There is no notion of subtree here. Instead, a lost
edge `t` cuts the tree `T` in two (`Below`, from a `TargetGeodesic.TreeRank`): no G-edge crosses the
cut, so `T̂` lies on one side of it because the marked core is connected (`iff_of_mem_gImage`),
while a leg crossing `t` exactly once has its two ends on opposite sides, by a handshake count mod
two on its stable path (`markSource_iff_not_centreSource`).

**How the parameter count is read** (section 6 below). Not as a dimension count but on the
length matrix, in the second form of §4.8, with Pairing and the column trick of §4.4: at the
inner end `w_j` of a lost leaf edge, trivalent of change zero, two columns agree on every G-row
unless a mark lies over `w_j`, and they cannot agree because the three lost columns already span
the leg rows. So the three marks lie over
the three `w_j`, and the leg leaves each mark up the lost edge there. This uses neither long legs
nor the positivity of the request.

**Connectedness.** The prose takes `G` connected (§4.1, which uses it to make `T̂ = φ(G)` a
subtree), and a cubic core with `p + 1 - n = 6` need not be connected. So `dichotomy` assumes
`core.Connected`, as do `Classification.dichotomy` and `classDichotomy`.

## Contents

| declaration | content | prose |
|---|---|---|
| `matrix_eq_zero_of_isLost`, `card_le_three_of_isLost` | **the lost-edge bound**, `\|L\| ≤ 3`, via `Utilities.DeterminantExpansion.card_le_of_cols_supported` | Lemma 4.5 |
| `nonDanglingValency_le_two_of_leaf`, `not_isLeafVertex_of_three_le` | over a leaf, nd-valency `≤ 2`; branch vertices are not over leaves | Part I `rem-leaves-min-change` |
| `stablePath_eq_of_isLeafEdge`, `isLost_of_leg_isLeafEdge` | survivors over a leaf edge lie on one stable path; a leg's leaf edge is lost | Lemma 4.4 |
| `markTarget_mem_gImage` | `φ(k) ∈ φ(G)` | definitions |
| `false_of_fourth_lost`, `isLost_iff_detour` | three detour leaf edges leave no room for a fourth lost edge | Theorem 4.7, Lemmas 4.4 and 4.5 |
| `not_isGlued_of_isClaw` | claw ⇒ not glued | Theorem 4.7(b) |
| `legEdge_injective_of_noDetour` | **leg shape**: a leg with no leaf detour passes over each target edge once (`RowGeodesic.rowTargetInjective_of_genusZero`) | Lemma 4.2(i) |
| `below_fst_iff_snd` | a tree cut at `t` separates exactly the ends of `t` | tree |
| `iff_of_mem_gImage` | a cut no G-edge crosses has `T̂` on one side (connected `G̃`) | §4.1 |
| `markSource_iff_not_centreSource` | a leg crossing a cut once has its ends on opposite sides | handshake mod 2 |
| `legEdge_not_isLost_of_noDetour` | such a leg stays in `φ(G)` when `φ(c) ∈ φ(G)` | Lemma 4.2(i), Theorem 4.7(a) |
| `legLength_le_of_noDetour` | **long legs leave `φ(G)`**: such a leg has length `≤ 4 L(G)` | Lemma 4.6 |
| `hasDetour_of_mem_gImage` | at long legs every leg has a leaf detour when `φ(c) ∈ φ(G)`, from the three above | Theorem 4.7(a) |
| `exists_triEdges` | the inner end of a lost leaf edge is trivalent, two edges in `T̂` | §4.8; `prop-local` |
| `matrix_eq_of_trivalent_of_noMark` | **Pairing**: with no mark there, the two `T̂`-columns agree on G-rows | §4.4; `prop-local` r0-nd2 |
| `false_of_matrix_eq` | **the column trick**: they cannot agree | §4.4, Lemma 4.5 (span) |
| `legEdge_target_of_mark_over` | at a mark over `w_j` the leg leaves up `λ_j` | `prop-local` r0-nd3 |
| `isGlued_of_lost_eq_detours` | **the parameter count**: each detour is at its own mark | Proposition 4.11, §4.8 |
| `dichotomy` | glued ↔ not claw | Theorem 4.7, Corollary 4.10; §4.8 |

The identity of Proposition 4.9 is not a separate declaration: it gives the values of `k₀`, which
the predicates here do not mention. The case split on `φ(c)` is the split between
the two directions.
-/

namespace GenusSixExistence.Tripod.Dichotomy

open DraismaVargas.Count
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount incidenceCount_pos_iff)
open DraismaVargas.LocalCases.FullDimensionalSource (FullDimensionalSourcePresentation)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open Utilities.DeterminantExpansion
open GenusSixExistence.Tripod.Gadget
open GenusSixExistence.Tripod.Classification

/-! ## 1.  Valency and leaves of the target -/

/-- In a loopless multigraph the valency is the number of incident edge occurrences. -/
theorem card_incidentEdges_eq_vertex_degree (T : CFGraph) (v : T.V) :
    ((GluingDatum.incidentEdges v).card : ℤ) = vertex_degree T v := by
  classical
  rw [DraismaVargas.Infrastructure.PendantDeletion.vertex_degree_eq_card_filter_incident]
  congr 1
  conv_rhs => rw [← Multiset.map_univ_coe T.edges]
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

theorem isLeafVertex_of_vertex_degree {T : CFGraph} {v : T.V} (h : vertex_degree T v = 1) :
    IsLeafVertex T v := by
  have := card_incidentEdges_eq_vertex_degree T v
  unfold IsLeafVertex
  omega

/-- A target edge is incident to each of its ends. -/
theorem mem_incidentEdges_fst {T : CFGraph} (t : T.edges) :
    t ∈ GluingDatum.incidentEdges (t : T.V × T.V).1 := by
  simp [GluingDatum.incidentEdges]

theorem mem_incidentEdges_snd {T : CFGraph} (t : T.edges) :
    t ∈ GluingDatum.incidentEdges (t : T.V × T.V).2 := by
  simp [GluingDatum.incidentEdges]

/-- A leaf edge is the leaf edge of one of its ends. -/
theorem exists_leaf_of_isLeafEdge {T : CFGraph} {t : T.edges} (ht : IsLeafEdge T t) :
    ∃ (v : T.V) (hv : IsLeafVertex T v), t = leafEdge hv := by
  rcases ht with h | h
  · exact ⟨_, isLeafVertex_of_vertex_degree h,
      eq_leafEdge_of_mem _ (mem_incidentEdges_fst t)⟩
  · exact ⟨_, isLeafVertex_of_vertex_degree h,
      eq_leafEdge_of_mem _ (mem_incidentEdges_snd t)⟩

section Leaves

variable {target : CFGraph} {deg : ℕ} {data : GluingDatum target deg}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (fd : FullDimensionalSourcePresentation data coordinate)

include fd in
/-- **Over a target leaf every source vertex has non-dangling valency at most two**
(Part I `rem-leaves-min-change`: the fold `A_v` has two, every other block none). -/
theorem nonDanglingValency_le_two_of_leaf {v : target.V} (hv : IsLeafVertex target v)
    (A : data.SourceVertex) (hA : A.1.1 = v) : nonDanglingValency data A ≤ 2 := by
  by_cases h : A = LeafFibre.coreVertex fd hv
  · rw [h, LeafFibre.nonDanglingValency_coreVertex fd hv]
  · rw [LeafFacetNoReturn.nonDanglingValency_eq_zero_of_ne_fold data fd
      (LeafFibre.coreVertex fd hv) A (by rw [hA]; rfl) hv
      (LeafFibre.nonDanglingValency_coreVertex fd hv) h]
    omega

include fd in
/-- A source vertex of non-dangling valency at least three is not over a leaf. -/
theorem not_isLeafVertex_of_three_le (A : data.SourceVertex)
    (hA : 3 ≤ nonDanglingValency data A) : ¬ IsLeafVertex target A.1.1 := fun hv ↦ by
  have := nonDanglingValency_le_two_of_leaf fd hv A rfl
  omega

include fd in
theorem vertex_degree_ne_one_of_three_le (A : data.SourceVertex)
    (hA : 3 ≤ nonDanglingValency data A) : vertex_degree target A.1.1 ≠ 1 := fun h ↦
  not_isLeafVertex_of_three_le fd A hA (isLeafVertex_of_vertex_degree h)

include fd in
/-- **Lemma 4.4, core.** All the surviving source edges over a leaf edge lie on one stable path:
the fold over the leaf is interior to a single stable path. -/
theorem stablePath_eq_of_isLeafEdge {t : target.edges} (ht : IsLeafEdge target t)
    (e e' : NonDanglingEdge data) (he : e.1.1.1 = t) (he' : e'.1.1.1 = t) :
    e.stablePath = e'.stablePath := by
  obtain ⟨v, hv, rfl⟩ := exists_leaf_of_isLeafEdge ht
  have h₁ := LeafFibre.stablePath_eq_of_mem_leafSurvivors fd hv
    ((LeafFibre.mem_leafSurvivors hv).mpr ⟨e.2, he⟩) e.2
  have h₂ := LeafFibre.stablePath_eq_of_mem_leafSurvivors fd hv
    ((LeafFibre.mem_leafSurvivors hv).mpr ⟨e'.2, he'⟩) e'.2
  exact h₁.trans h₂.symm

end Leaves

/-- The target of a source vertex is an end of the target edge of every incident source
edge. -/
theorem incident_target {target : CFGraph} {deg : ℕ} {data : GluingDatum target deg}
    {e : data.SourceEdge} {A : data.SourceVertex} (h : Incident data e A) :
    (e.1.1 : target.V × target.V).1 = A.1.1 ∨ (e.1.1 : target.V × target.V).2 = A.1.1 := by
  rcases h with h | h
  · exact Or.inl (congrArg (fun B : data.SourceVertex ↦ B.1.1) h)
  · exact Or.inr (congrArg (fun B : data.SourceVertex ↦ B.1.1) h)

/-- A source vertex of positive non-dangling valency carries a non-dangling edge. -/
theorem exists_nonDanglingEdge_incident {target : CFGraph} {deg : ℕ}
    {data : GluingDatum target deg} (A : data.SourceVertex)
    (hA : 0 < nonDanglingValency data A) :
    ∃ e : NonDanglingEdge data, Incident data e.1 A := by
  rw [← card_nonDanglingIncident, Finset.card_pos] at hA
  obtain ⟨e, he⟩ := hA
  rw [mem_nonDanglingIncident] at he
  exact ⟨⟨e, he.1⟩, he.2⟩

/-- Two distinct blocks of a sheet partition have at most `d` sheets between them. -/
theorem blockCard_add_blockCard_le {d : ℕ} (P : SheetPartition d) {a b : Fin d}
    (ha : P.repr a = a) (hb : P.repr b = b) (hab : a ≠ b) :
    P.blockCard a + P.blockCard b ≤ d := by
  classical
  unfold SheetPartition.blockCard
  rw [← Finset.card_union_of_disjoint]
  · exact (Finset.card_le_univ _).trans (by simp)
  · rw [Finset.disjoint_left]
    intro j hja hjb
    rw [SheetPartition.mem_block_iff, SheetPartition.rel_iff] at hja hjb
    exact hab (by rw [← ha, ← hb, hja, hjb])

/-- Two distinct source edges over one target edge have indices adding up to at most the
degree. -/
theorem sourceEdgeIndex_add_le {target : CFGraph} {deg : ℕ} (data : GluingDatum target deg)
    (e e' : data.SourceEdge) (hT : e.1.1 = e'.1.1) (hne : e ≠ e') :
    data.sourceEdgeIndex e + data.sourceEdgeIndex e' ≤ deg := by
  obtain ⟨⟨t, i⟩, hi⟩ := e
  obtain ⟨⟨t', i'⟩, hi'⟩ := e'
  simp only at hT
  subst hT
  have hii : i ≠ i' := fun h ↦ hne (by subst h; rfl)
  exact blockCard_add_blockCard_le (data.edgePartition t) hi hi' hii

/-! ## 2.  Lost edges and the lost-edge bound (Lemma 4.5) -/

section Lost

variable {n p degree : ℕ} {core : Core n p} {s : MarkSlots p}
variable (κ : Frame (tripodCore core s) degree)

/-- **A lost target edge** (§4.1): no non-dangling source edge of a G-slot lies over it. -/
def IsLost (t : κ.target.edges) : Prop :=
  ∀ e : NonDanglingEdge κ.data, IsGSlot (κ.ident.row e.stablePath) → e.1.1.1 ≠ t

/-- The matrix row of a stable path is read as the core slot `κ.slot`. -/
theorem ident_row_eq_slot (e : NonDanglingEdge κ.data) :
    κ.ident.row e.stablePath = κ.slot (κ.fullDim.labelling.row e.stablePath) := by
  simp [Frame.slot]

/-- **A lost column vanishes on every G-row** (Lemma 4.5, first half): the entry is a sum
over the row's surviving edges above the column's target edge, and there are none. -/
theorem matrix_eq_zero_of_isLost {t : κ.target.edges} (ht : IsLost κ t) (r : Fin (p + 1 + 1 + 1 + 3))
    (hr : IsGSlot (κ.slot r)) :
    κ.matrix r (κ.fullDim.labelling.targetEdge.symm t) = 0 := by
  unfold Frame.matrix
  rw [LeafFibre.matrix_eq_sum_fibre]
  refine Finset.sum_eq_zero fun e he ↦ ?_
  obtain ⟨⟨hSurv, hRow⟩, hT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp he
  exfalso
  have hRow' : κ.ident.row (NonDanglingEdge.stablePath (⟨e, hSurv⟩ : NonDanglingEdge κ.data)) =
      κ.slot r := by
    rw [← hRow]
    show κ.ident.row _ = κ.ident.row (κ.fullDim.labelling.row.symm (κ.fullDim.labelling.row _))
    rw [Equiv.symm_apply_apply]
  exact ht ⟨e, hSurv⟩ (hRow' ▸ hr) hT

instance (j : Fin (p + 1 + 1 + 1 + 3)) : Decidable (IsGSlot j) :=
  inferInstanceAs (Decidable (j.val < p + 1 + 1 + 1))

/-- The leg rows: the matrix rows whose core slot is not a G-slot. At most three. -/
theorem card_legRows_le :
    ((Finset.univ : Finset (Fin (p + 1 + 1 + 1 + 3))).filter
      fun r ↦ ¬ IsGSlot (κ.slot r)).card ≤ 3 := by
  classical
  calc ((Finset.univ : Finset (Fin (p + 1 + 1 + 1 + 3))).filter
        fun r ↦ ¬ IsGSlot (κ.slot r)).card
      = (((Finset.univ : Finset (Fin (p + 1 + 1 + 1 + 3))).filter
          fun r ↦ ¬ IsGSlot (κ.slot r)).map κ.slot.toEmbedding).card := (Finset.card_map _).symm
    _ ≤ ((Finset.univ : Finset (Fin 3)).image (legSlot p)).card := by
        refine Finset.card_le_card fun j hj ↦ ?_
        obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hj
        have hr' : ¬ IsGSlot (κ.slot r) := (Finset.mem_filter.mp hr).2
        refine Finset.mem_image.mpr ⟨⟨(κ.slot r).val - (p + 1 + 1 + 1), by omega⟩,
          Finset.mem_univ _, ?_⟩
        unfold IsGSlot at hr'
        apply Fin.ext
        simp only [legSlot, Fin.val_natAdd, Equiv.coe_toEmbedding]
        omega
    _ ≤ 3 := Finset.card_image_le.trans (by simp)

/-- **The lost-edge bound** (Lemma 4.5): at most three target edges are lost. The lost
columns are supported on the three leg rows, and the length matrix is nonsingular. -/
theorem card_le_three_of_isLost (S : Finset κ.target.edges) (hS : ∀ t ∈ S, IsLost κ t) :
    S.card ≤ 3 := by
  classical
  have hC := card_le_of_cols_supported κ.matrix κ.det_ne_zero
    (S.map κ.fullDim.labelling.targetEdge.symm.toEmbedding)
    ((Finset.univ : Finset (Fin (p + 1 + 1 + 1 + 3))).filter fun r ↦ ¬ IsGSlot (κ.slot r))
    (by
      intro c hc r hr
      obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hc
      have hG : IsGSlot (κ.slot r) := by
        by_contra hG
        exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩)
      exact matrix_eq_zero_of_isLost κ (hS t ht) r hG)
  rw [Finset.card_map] at hC
  exact hC.trans (card_legRows_le κ)

/-! ## 3.  Marks, legs and the centre -/

/-- The G-slot of the marked core leaving mark `k` (the second piece of the slot split at
`k`). -/
def markGSlot (p : ℕ) : Fin 3 → Fin (p + 1 + 1 + 1 + 3)
  | 0 => Fin.castAdd 3 (Fin.last p).castSucc.castSucc
  | 1 => Fin.castAdd 3 (Fin.last (p + 1)).castSucc
  | 2 => Fin.castAdd 3 (Fin.last (p + 1 + 1))

theorem isGSlot_markGSlot (k : Fin 3) : IsGSlot (markGSlot p k) := by
  unfold IsGSlot
  fin_cases k
  · show p < p + 1 + 1 + 1; omega
  · show p + 1 < p + 1 + 1 + 1; omega
  · show p + 1 + 1 < p + 1 + 1 + 1; omega

theorem tail_markGSlot (core : Core n p) (s : MarkSlots p) (k : Fin 3) :
    (tripodCore core s).tail (markGSlot p k) = tripodMark n k := by
  unfold tripodCore tripodMark markedCore
  fin_cases k
  · simp only [markGSlot, attachTripod_tail_castAdd, subdivide_tail_castSucc,
      subdivide_tail_last]
    congr 1
  · simp only [markGSlot, attachTripod_tail_castAdd, subdivide_tail_castSucc,
      subdivide_tail_last]
    congr 1
  · simp only [markGSlot, attachTripod_tail_castAdd, subdivide_tail_last]
    congr 1

/-- **`φ(k) ∈ φ(G)`**: the mark carries a non-dangling edge of a G-slot. -/
theorem markTarget_mem_gImage (k : Fin 3) :
    (TripodFrame.markSource κ k).1.1 ∈ TripodFrame.gImage κ := by
  classical
  have hInc := κ.ident.incidence (κ.ident.vertex.symm (tripodMark n k)) (markGSlot p k)
  rw [Equiv.apply_symm_apply] at hInc
  have hPos : 0 < incidenceCount κ.data (κ.ident.vertex.symm (tripodMark n k)).1
      (κ.ident.row.symm (markGSlot p k)) := by
    rw [hInc]
    unfold coreIncidence
    rw [ite_eq_left (tail_markGSlot core s k)]
    omega
  obtain ⟨e, hE, hPath⟩ := (incidenceCount_pos_iff _ _ _).mp hPos
  refine ⟨e, ?_, incident_target hE⟩
  rw [hPath, Equiv.apply_symm_apply]
  exact isGSlot_markGSlot k

/-- The source vertex under the centre. -/
def centreSource : κ.data.SourceVertex := (κ.ident.vertex.symm (centre n)).1

theorem three_le_centreSource : 3 ≤ nonDanglingValency κ.data (centreSource κ) :=
  (κ.ident.vertex.symm (centre n)).2

theorem three_le_markSource (k : Fin 3) :
    3 ≤ nonDanglingValency κ.data (TripodFrame.markSource κ k) :=
  (κ.ident.vertex.symm (tripodMark n k)).2

theorem legSlot_injective : Function.Injective (legSlot p) := by
  intro j k h
  have := congrArg Fin.val h
  simp only [legSlot, Fin.val_natAdd] at this
  exact Fin.ext (by omega)

/-- **Lemma 4.4**: a leaf edge under an edge of leg `k` is lost. -/
theorem isLost_of_leg_isLeafEdge (k : Fin 3) (e : NonDanglingEdge κ.data)
    (hRow : κ.ident.row e.stablePath = legSlot p k) (hLeaf : IsLeafEdge κ.target e.1.1.1) :
    IsLost κ e.1.1.1 := by
  intro e' hG he'
  have := stablePath_eq_of_isLeafEdge κ.fullDim hLeaf e' e he' rfl
  rw [this, hRow] at hG
  exact legSlot_not_isGSlot k hG

/-- Two legs over one leaf edge are the same leg (Lemma 4.4: one stable path over a leaf). -/
theorem leg_eq_of_isLeafEdge {j k : Fin 3} (e e' : NonDanglingEdge κ.data)
    (hRow : κ.ident.row e.stablePath = legSlot p j)
    (hRow' : κ.ident.row e'.stablePath = legSlot p k) (hLeaf : IsLeafEdge κ.target e.1.1.1)
    (hEq : e'.1.1.1 = e.1.1.1) : j = k := by
  have := stablePath_eq_of_isLeafEdge κ.fullDim hLeaf e e' rfl hEq
  rw [this, hRow'] at hRow
  exact legSlot_injective hRow.symm

/-- **No fourth lost edge.** If every leg `k` has an edge `e k` over a leaf edge, these three
leaf edges are distinct and lost (Lemma 4.4), so a further lost edge would make four, against
the lost-edge bound (Lemma 4.5). -/
theorem false_of_fourth_lost (e : Fin 3 → NonDanglingEdge κ.data)
    (hRow : ∀ k, κ.ident.row (e k).stablePath = legSlot p k)
    (hLeaf : ∀ k, IsLeafEdge κ.target (e k).1.1.1) {t : κ.target.edges} (ht : IsLost κ t)
    (hNe : ∀ k, t ≠ (e k).1.1.1) : False := by
  classical
  let g : Option (Fin 3) → κ.target.edges := fun o ↦ o.elim t fun k ↦ (e k).1.1.1
  have hg : Function.Injective g := by
    rintro (_ | j) (_ | k) h
    · rfl
    · exact absurd h (hNe k)
    · exact absurd h.symm (hNe j)
    · exact congrArg some (leg_eq_of_isLeafEdge κ (e j) (e k) (hRow j) (hRow k) (hLeaf j) h.symm)
  have hLost : ∀ u ∈ (Finset.univ : Finset (Option (Fin 3))).image g, IsLost κ u := by
    intro u hu
    obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp hu
    rcases o with _ | k
    · exact ht
    · exact isLost_of_leg_isLeafEdge κ k (e k) (hRow k) (hLeaf k)
  have hCard := card_le_three_of_isLost κ _ hLost
  rw [Finset.card_image_of_injective _ hg] at hCard
  simp at hCard

/-- **The detour leaf edges are exactly the lost edges** (Theorem 4.7(a), second bullet). -/
theorem isLost_iff_detour (e : Fin 3 → NonDanglingEdge κ.data)
    (hRow : ∀ k, κ.ident.row (e k).stablePath = legSlot p k)
    (hLeaf : ∀ k, IsLeafEdge κ.target (e k).1.1.1) (t : κ.target.edges) :
    IsLost κ t ↔ ∃ k, t = (e k).1.1.1 := by
  constructor
  · intro ht
    by_contra hNo
    push Not at hNo
    exact false_of_fourth_lost κ e hRow hLeaf ht hNo
  · rintro ⟨k, rfl⟩
    exact isLost_of_leg_isLeafEdge κ k (e k) (hRow k) (hLeaf k)

/-! ## 4.  Claw ⇒ not glued (Theorem 4.7(b)) -/

/-- **A claw frame is not glued** (Theorem 4.7(b), in the form needed here). If every leg left its
mark up a leaf edge `h_k`, then the `h_k` and an edge at `φ(c)` would be four lost edges. No
hypothesis on the degree, the core or the request. -/
theorem not_isGlued_of_isClaw (hClaw : TripodFrame.IsClaw κ) : ¬ TripodFrame.IsGlued κ := by
  classical
  intro hGlued
  choose e hRow hInc hLeaf using hGlued
  -- the centre carries a non-dangling edge, over a target edge `f` at `φ(c)`
  obtain ⟨ec, hec⟩ := exists_nonDanglingEdge_incident (centreSource κ)
    (by have := three_le_centreSource κ; omega)
  have hcEnd := incident_target hec
  have hcNotLeaf := vertex_degree_ne_one_of_three_le κ.fullDim _ (three_le_centreSource κ)
  -- `f` is lost: anything of `G` over it would put `φ(c)` in `φ(G)`
  have hfLost : IsLost κ ec.1.1.1 := by
    intro e' hG he'
    apply hClaw
    refine ⟨e', hG, ?_⟩
    rw [he']
    exact hcEnd
  -- `f` is none of the `h_k`
  have hfNe : ∀ k, ec.1.1.1 ≠ (e k).1.1.1 := by
    intro k hEq
    have hkEnd := incident_target (hInc k)
    have hkNotLeaf := vertex_degree_ne_one_of_three_le κ.fullDim _ (three_le_markSource κ k)
    have hkG := markTarget_mem_gImage κ k
    have hNe : (TripodFrame.markSource κ k).1.1 ≠ TripodFrame.centreTarget κ :=
      fun h ↦ hClaw (h ▸ hkG)
    have hcEnd' : ((e k).1.1.1 : κ.target.V × κ.target.V).1 = TripodFrame.centreTarget κ ∨
        ((e k).1.1.1 : κ.target.V × κ.target.V).2 = TripodFrame.centreTarget κ := by
      rw [← hEq]; exact hcEnd
    have hLeafk := hLeaf k
    unfold IsLeafEdge at hLeafk
    change vertex_degree κ.target (TripodFrame.centreTarget κ) ≠ 1 at hcNotLeaf
    rcases hkEnd with h₁ | h₁ <;> rcases hcEnd' with h₂ | h₂
    · exact hNe (h₁.symm.trans h₂)
    · rcases hLeafk with h | h
      · rw [h₁] at h; exact hkNotLeaf h
      · rw [h₂] at h; exact hcNotLeaf h
    · rcases hLeafk with h | h
      · rw [h₂] at h; exact hcNotLeaf h
      · rw [h₁] at h; exact hkNotLeaf h
    · exact hNe (h₁.symm.trans h₂)
  exact false_of_fourth_lost κ e hRow hLeaf hfLost hfNe

end Lost

/-! ## 5.  The cut at a lost edge (§4.1: `T̂` is a subtree)

A target edge `t` of the tree `T` cuts it in two: `Below A t` is the side of the larger end of
`t` for a tree rank `A`. A target predicate that no G-edge crosses is constant on `T̂ = φ(G)`,
because the marked core is connected (`iff_of_mem_gImage`), and a leg crossing the cut once has
its two ends on opposite sides, by a handshake count mod two (`markSource_iff_not_centreSource`). -/

/-! ### The cut of a tree at one edge -/

section TreeCut

open DraismaVargas.Count.TargetGeodesic

variable {G : CFGraph.{0}} (A : TreeRank G)

/-- The vertices **below** the edge `t`: those whose chain of parents reaches the larger end of
`t`. Removing `t` separates them from the rest. -/
def Below (t : G.edges) (v : G.V) : Prop := ∃ j : ℕ, A.up^[j] v = A.high t

theorem below_low_iff_below_high {t u : G.edges} (h : u ≠ t) :
    Below A t (A.low u) ↔ Below A t (A.high u) := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j + 1, by rw [Function.iterate_succ_apply, A.up_high]; exact hj⟩
  · rintro ⟨j, hj⟩
    cases j with
    | zero => exact absurd (A.high_injective hj) h
    | succ j =>
        rw [Function.iterate_succ_apply, A.up_high] at hj
        exact ⟨j, hj⟩

theorem below_high_self (t : G.edges) : Below A t (A.high t) := ⟨0, rfl⟩

theorem not_below_low_self (t : G.edges) : ¬ Below A t (A.low t) := by
  rintro ⟨j, hj⟩
  have h1 := A.rank_iterate_up_le j (A.low t)
  rw [hj] at h1
  exact absurd (A.rank_low_lt t) (not_lt.mpr h1)

/-- **The cut at `t` separates the two ends of `u` exactly when `u = t`.** -/
theorem below_fst_iff_snd (t u : G.edges) :
    (Below A t (u : G.V × G.V).1 ↔ Below A t (u : G.V × G.V).2) ↔ u ≠ t := by
  rcases A.ends u with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · constructor
    · intro hiff hut
      subst hut
      exact not_below_low_self A u (hiff.mpr (below_high_self A u))
    · exact below_low_iff_below_high A
  · constructor
    · intro hiff hut
      subst hut
      exact not_below_low_self A u (hiff.mp (below_high_self A u))
    · intro h
      exact (below_low_iff_below_high A h).symm

end TreeCut

/-! ### A target predicate along the source -/

section SourceCut

variable {target : CFGraph.{0}} {deg : ℕ} {data : GluingDatum target deg}

/-- If a target predicate agrees on the two ends of the target edge of `f`, it agrees on the
targets of any two source vertices incident to `f`. -/
theorem iff_of_incident_of_iff {Q : target.V → Prop} {f : data.SourceEdge}
    (hf : Q (f.1.1 : target.V × target.V).1 ↔ Q (f.1.1 : target.V × target.V).2)
    {X Y : data.SourceVertex} (hX : Incident data f X) (hY : Incident data f Y) :
    Q X.1.1 ↔ Q Y.1.1 := by
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · exact Iff.rfl
  · exact hf
  · exact hf.symm
  · exact Iff.rfl

/-- **A target predicate is constant along a stable path none of whose edges it separates.** -/
theorem iff_of_stablePath_eq {Q : target.V → Prop} {L : StablePath data}
    (hL : ∀ a : NonDanglingEdge data, a.stablePath = L →
      (Q (a.1.1.1 : target.V × target.V).1 ↔ Q (a.1.1.1 : target.V × target.V).2))
    {a b : NonDanglingEdge data} (ha : a.stablePath = L) (hb : b.stablePath = L)
    {X Y : data.SourceVertex} (hX : Incident data a.1 X) (hY : Incident data b.1 Y) :
    Q X.1.1 ↔ Q Y.1.1 := by
  have hClosed : ∀ first second : NonDanglingEdge data, Consecutive data first second →
      (first.stablePath = L ∧ Q (data.sourceEnds first.1).1.1.1) →
      (second.stablePath = L ∧ Q (data.sourceEnds second.1).1.1.1) := by
    rintro first second hCons ⟨hfL, hfQ⟩
    have hsL : second.stablePath = L := (stablePath_eq_of_consecutive hCons).symm.trans hfL
    obtain ⟨-, M, hfM, hsM, -⟩ := hCons
    refine ⟨hsL, ?_⟩
    have h1 := iff_of_incident_of_iff (hL first hfL) (incident_left data first.1) hfM
    have h2 := iff_of_incident_of_iff (hL second hsL) hsM (incident_left data second.1)
    exact h2.mp (h1.mp hfQ)
  have hEqv := (stablePath_eq_iff a b).mp (ha.trans hb.symm)
  have hab := eqvGen_iff_of_closed
    (property := fun e ↦ e.stablePath = L ∧ Q (data.sourceEnds e.1).1.1.1) hClosed hEqv
  have hX' := iff_of_incident_of_iff (hL a ha) hX (incident_left data a.1)
  have hY' := iff_of_incident_of_iff (hL b hb) (incident_left data b.1) hY
  constructor
  · intro hQX
    exact hY'.mp ((hab.mp ⟨ha, hX'.mp hQX⟩).2)
  · intro hQY
    exact hX'.mpr ((hab.mpr ⟨hb, hY'.mpr hQY⟩).2)

/-- The two ends of a source edge, counted by a target predicate. -/
theorem sum_ite_incident (Q : target.V → Prop) [DecidablePred Q] (f : data.SourceEdge) :
    (∑ X : data.SourceVertex, if Q X.1.1 ∧ Incident data f X then 1 else 0 : ℕ) =
      (if Q (f.1.1 : target.V × target.V).1 then 1 else 0) +
        (if Q (f.1.1 : target.V × target.V).2 then 1 else 0) := by
  classical
  have hNe := data.sourceEnds_ne f
  have hPoint : ∀ X : data.SourceVertex, (if Q X.1.1 ∧ Incident data f X then 1 else 0 : ℕ) =
      (if (data.sourceEnds f).1 = X then (if Q (f.1.1 : target.V × target.V).1 then 1 else 0)
        else 0) +
      (if (data.sourceEnds f).2 = X then (if Q (f.1.1 : target.V × target.V).2 then 1 else 0)
        else 0) := by
    intro X
    by_cases h1 : (data.sourceEnds f).1 = X
    · subst h1
      have h2 : (data.sourceEnds f).2 ≠ (data.sourceEnds f).1 := fun h ↦ hNe h.symm
      simp only [incident_left, and_true, ite_true, h2, ite_false, add_zero]
      rfl
    · by_cases h2 : (data.sourceEnds f).2 = X
      · subst h2
        simp only [incident_right, and_true, ite_true, h1, ite_false, zero_add]
        rfl
      · have hI : ¬ Incident data f X := by
          rintro (h | h)
          · exact h1 h
          · exact h2 h
        simp [hI, h1, h2]
  rw [Finset.sum_congr rfl fun X _ ↦ hPoint X, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq]
  simp

/-- **The handshake count of a stable path against a target predicate.** -/
theorem sum_ite_incidenceCount (Q : target.V → Prop) [DecidablePred Q] (L : StablePath data) :
    (∑ X : data.SourceVertex, if Q X.1.1 then incidenceCount data X L else 0) =
      ∑ a : NonDanglingEdge data, if a.stablePath = L then
        ((if Q (a.1.1.1 : target.V × target.V).1 then 1 else 0) +
          (if Q (a.1.1.1 : target.V × target.V).2 then 1 else 0)) else 0 := by
  classical
  have hCount : ∀ X : data.SourceVertex, incidenceCount data X L =
      ∑ a : NonDanglingEdge data, if Incident data a.1 X ∧ a.stablePath = L then 1 else 0 := by
    intro X
    unfold incidenceCount StablePathCount.incidentEdges
    rw [Finset.filter_filter, Finset.card_filter]
  calc (∑ X : data.SourceVertex, if Q X.1.1 then incidenceCount data X L else 0)
      = ∑ X : data.SourceVertex, ∑ a : NonDanglingEdge data,
          if a.stablePath = L then (if Q X.1.1 ∧ Incident data a.1 X then 1 else 0)
          else 0 := by
        refine Finset.sum_congr rfl fun X _ ↦ ?_
        rw [hCount X]
        by_cases hQ : Q X.1.1
        · rw [ite_eq_left hQ]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          by_cases h1 : Incident data a.1 X <;> by_cases h2 : a.stablePath = L <;>
            simp [h1, h2, hQ]
        · rw [ite_eq_right hQ]
          symm
          exact Finset.sum_eq_zero fun a _ ↦ by simp [hQ]
    _ = ∑ a : NonDanglingEdge data, ∑ X : data.SourceVertex,
          if a.stablePath = L then (if Q X.1.1 ∧ Incident data a.1 X then 1 else 0)
          else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        by_cases hL : a.stablePath = L
        · simp only [hL, ite_true]
          exact sum_ite_incident Q a.1
        · simp [hL]

end SourceCut

/-! ### On the gadget: the two ends of a leg, and the image of `G` -/

section GadgetCut

variable {n p degree : ℕ} {core : Core n p} {s : MarkSlots p}

/-- The marked core is connected when `G̃` is. -/
theorem markedCore_connected (hconn : core.Connected) : (markedCore core s).Connected :=
  subdivide_connected _ _ (subdivide_connected _ _ (subdivide_connected _ _ hconn))

theorem tripodCore_tail_castAdd (i : Fin (p + 1 + 1 + 1)) :
    (tripodCore core s).tail (Fin.castAdd 3 i) = ((markedCore core s).tail i).castSucc :=
  attachTripod_tail_castAdd _ _ i

theorem tripodCore_head_castAdd (i : Fin (p + 1 + 1 + 1)) :
    (tripodCore core s).head (Fin.castAdd 3 i) = ((markedCore core s).head i).castSucc :=
  attachTripod_head_castAdd _ _ i

theorem tripodCore_tail_legSlot (k : Fin 3) :
    (tripodCore core s).tail (legSlot p k) = centre n :=
  attachTripod_tail_natAdd _ _ k

theorem tripodCore_head_legSlot (k : Fin 3) :
    (tripodCore core s).head (legSlot p k) = tripodMark n k :=
  attachTripod_head_natAdd _ _ k

/-- The stable path of a slot meets the branch vertex at each of its ends. -/
theorem exists_incident_of_end {N P : ℕ} {C : Core N P} (κ : Frame C degree) (j : Fin P)
    (v : Fin N) (hv : C.tail j = v ∨ C.head j = v) :
    ∃ a : NonDanglingEdge κ.data, Incident κ.data a.1 (κ.ident.vertex.symm v).1 ∧
      a.stablePath = κ.ident.row.symm j := by
  have hInc := κ.ident.incidence (κ.ident.vertex.symm v) j
  rw [Equiv.apply_symm_apply] at hInc
  have hPos : 0 < incidenceCount κ.data (κ.ident.vertex.symm v).1 (κ.ident.row.symm j) := by
    rw [hInc]
    unfold coreIncidence
    rcases hv with h | h
    · rw [ite_eq_left h]; omega
    · rw [ite_eq_left h]; omega
  exact (incidenceCount_pos_iff _ _ _).mp hPos

/-- **`T̂ = φ(G)` lies on one side of every cut that no G-edge crosses** (§4.1: `T̂` is
connected because `G` is). The cut is any target predicate that agrees on the two ends of the
target edge of every G-edge. -/
theorem iff_of_mem_gImage (hconn : core.Connected) (κ : Frame (tripodCore core s) degree)
    {Q : κ.target.V → Prop}
    (hQ : ∀ a : NonDanglingEdge κ.data, IsGSlot (κ.ident.row a.stablePath) →
      (Q (a.1.1.1 : κ.target.V × κ.target.V).1 ↔ Q (a.1.1.1 : κ.target.V × κ.target.V).2))
    {x x' : κ.target.V} (hx : x ∈ TripodFrame.gImage κ) (hx' : x' ∈ TripodFrame.gImage κ) :
    Q x ↔ Q x' := by
  classical
  -- the branch vertex over a vertex of the marked core
  let β : Fin (n + 1 + 1 + 1) → κ.data.SourceVertex :=
    fun v ↦ (κ.ident.vertex.symm v.castSucc).1
  -- along a G-slot the predicate is constant
  have hRow : ∀ (i : Fin (p + 1 + 1 + 1)) {a b : NonDanglingEdge κ.data},
      a.stablePath = κ.ident.row.symm (Fin.castAdd 3 i) →
      b.stablePath = κ.ident.row.symm (Fin.castAdd 3 i) → ∀ {X Y : κ.data.SourceVertex},
      Incident κ.data a.1 X → Incident κ.data b.1 Y → (Q X.1.1 ↔ Q Y.1.1) := by
    intro i a b ha hb X Y hX hY
    refine iff_of_stablePath_eq (L := κ.ident.row.symm (Fin.castAdd 3 i)) ?_ ha hb hX hY
    intro c hc
    apply hQ c
    rw [hc, Equiv.apply_symm_apply]
    show (Fin.castAdd 3 i).val < p + 1 + 1 + 1
    exact i.isLt
  -- the two ends of a slot of the marked core agree
  have hSlot : ∀ i : Fin (p + 1 + 1 + 1),
      Q (β ((markedCore core s).tail i)).1.1 ↔ Q (β ((markedCore core s).head i)).1.1 := by
    intro i
    obtain ⟨a, haX, ha⟩ := exists_incident_of_end κ (Fin.castAdd 3 i)
      ((markedCore core s).tail i).castSucc (Or.inl (tripodCore_tail_castAdd i))
    obtain ⟨b, hbY, hb⟩ := exists_incident_of_end κ (Fin.castAdd 3 i)
      ((markedCore core s).head i).castSucc (Or.inr (tripodCore_head_castAdd i))
    exact hRow i ha hb haX hbY
  -- so, by connectedness, all the branch vertices of the marked core agree
  have hAll : ∀ v w : Fin (n + 1 + 1 + 1), Q (β v).1.1 ↔ Q (β w).1.1 := by
    intro v w
    by_contra hvw
    let S : Finset (Fin (n + 1 + 1 + 1)) := Finset.univ.filter fun u ↦ Q (β u).1.1
    have hmem : ∀ u, u ∈ S ↔ Q (β u).1.1 := fun u ↦ by simp [S]
    have hS : ∃ v w : Fin (n + 1 + 1 + 1), v ∈ S ∧ w ∉ S := by
      by_cases hv : Q (β v).1.1
      · refine ⟨v, w, (hmem v).mpr hv, fun hw ↦ hvw ⟨fun _ ↦ (hmem w).mp hw, fun _ ↦ hv⟩⟩
      · refine ⟨w, v, (hmem w).mpr ?_, fun h ↦ hv ((hmem v).mp h)⟩
        by_contra hw
        exact hvw ⟨fun h ↦ absurd h hv, fun h ↦ absurd h hw⟩
    obtain ⟨i, hi⟩ := markedCore_connected hconn S hS
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 ((hmem _).mpr ((hSlot i).mp ((hmem _).mp h1)))
    · exact h2 ((hmem _).mpr ((hSlot i).mpr ((hmem _).mp h1)))
  -- every point of `T̂` agrees with some branch vertex of the marked core
  have hEnd : ∀ y ∈ TripodFrame.gImage κ, ∃ v : Fin (n + 1 + 1 + 1), Q y ↔ Q (β v).1.1 := by
    rintro y ⟨e, hG, hy⟩
    let i : Fin (p + 1 + 1 + 1) := ⟨(κ.ident.row e.stablePath).val, hG⟩
    have he : e.stablePath = κ.ident.row.symm (Fin.castAdd 3 i) := by
      rw [Equiv.eq_symm_apply]
      exact Fin.ext rfl
    obtain ⟨a, haX, ha⟩ := exists_incident_of_end κ (Fin.castAdd 3 i)
      ((markedCore core s).tail i).castSucc (Or.inl (tripodCore_tail_castAdd i))
    refine ⟨(markedCore core s).tail i, ?_⟩
    rcases hy with hy | hy
    · rw [← hy]
      exact hRow i he ha (incident_left κ.data e.1) haX
    · rw [← hy]
      exact hRow i he ha (incident_right κ.data e.1) haX
  obtain ⟨v, hv⟩ := hEnd x hx
  obtain ⟨w, hw⟩ := hEnd x' hx'
  exact hv.trans ((hAll v w).trans hw.symm)

/-- **The incidences of a leg, mod two**: a source vertex meets the stable path of leg `k` an odd
number of times exactly when it is the centre or mark `k`. -/
theorem incidenceCount_leg (κ : Frame (tripodCore core s) degree) (k : Fin 3)
    (X : κ.data.SourceVertex) :
    (incidenceCount κ.data X (κ.ident.row.symm (legSlot p k)) : ZMod 2) =
      (if X = centreSource κ then 1 else 0) +
        (if X = TripodFrame.markSource κ k then 1 else 0) := by
  classical
  rcases Nat.lt_or_ge (nonDanglingValency κ.data X) 3 with hX | hX
  · -- not a branch vertex: it meets each stable path an even number of times
    have hc : X ≠ centreSource κ := fun h ↦ by
      have := three_le_centreSource κ
      rw [← h] at this
      omega
    have hm : X ≠ TripodFrame.markSource κ k := fun h ↦ by
      have := three_le_markSource κ k
      rw [← h] at this
      omega
    rw [ite_eq_right hc, ite_eq_right hm, add_zero]
    rcases Nat.lt_or_ge (nonDanglingValency κ.data X) 2 with h2 | h2
    · have h1 := NonDanglingValency.nonDanglingValency_ne_one κ.data κ.fullDim.connected X
      have h0 : nonDanglingValency κ.data X = 0 := by omega
      have hle : incidenceCount κ.data X (κ.ident.row.symm (legSlot p k)) ≤
          nonDanglingValency κ.data X := by
        rw [← StablePathCount.sum_incidenceCount_vertex]
        exact Finset.single_le_sum (f := fun path ↦ incidenceCount κ.data X path)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
      have : incidenceCount κ.data X (κ.ident.row.symm (legSlot p k)) = 0 := by omega
      rw [this, Nat.cast_zero]
    · have hval : nonDanglingValency κ.data X = 2 := by omega
      rcases StablePathCount.incidenceCount_eq_zero_or_two κ.data hval
        (κ.ident.row.symm (legSlot p k)) with h | h
      · rw [h, Nat.cast_zero]
      · rw [h]
        decide
  · -- a branch vertex: the core counts its incidences
    let b : StableGraphIncidence.BranchVertex κ.data := ⟨X, hX⟩
    have hInc := κ.ident.incidence b (legSlot p k)
    have hX' : b.1 = X := rfl
    rw [hX'] at hInc
    rw [hInc]
    unfold coreIncidence
    rw [tripodCore_tail_legSlot, tripodCore_head_legSlot]
    have hcIff : (centre n = κ.ident.vertex b) ↔ X = centreSource κ := by
      constructor
      · intro h
        show X = (κ.ident.vertex.symm (centre n)).1
        rw [h, Equiv.symm_apply_apply]
      · intro h
        have : b = κ.ident.vertex.symm (centre n) := Subtype.ext h
        rw [this, Equiv.apply_symm_apply]
    have hmIff : (tripodMark n k = κ.ident.vertex b) ↔ X = TripodFrame.markSource κ k := by
      constructor
      · intro h
        show X = (κ.ident.vertex.symm (tripodMark n k)).1
        rw [h, Equiv.symm_apply_apply]
      · intro h
        have : b = κ.ident.vertex.symm (tripodMark n k) := Subtype.ext h
        rw [this, Equiv.apply_symm_apply]
    by_cases h1 : X = centreSource κ <;> by_cases h2 : X = TripodFrame.markSource κ k <;>
      simp [hcIff, hmIff, h1, h2]

/-- **A leg crosses a cut an odd number of times exactly when its ends are on opposite sides.**
If exactly one edge of leg `k` has its target edge's ends on opposite sides of a target
predicate, then mark `k` and the centre lie on opposite sides. -/
theorem markSource_iff_not_centreSource (κ : Frame (tripodCore core s) degree) (k : Fin 3)
    (Q : κ.target.V → Prop) (e : NonDanglingEdge κ.data)
    (he : κ.ident.row e.stablePath = legSlot p k)
    (hQe : ¬ (Q (e.1.1.1 : κ.target.V × κ.target.V).1 ↔
      Q (e.1.1.1 : κ.target.V × κ.target.V).2))
    (hOther : ∀ a : NonDanglingEdge κ.data, κ.ident.row a.stablePath = legSlot p k → a ≠ e →
      (Q (a.1.1.1 : κ.target.V × κ.target.V).1 ↔ Q (a.1.1.1 : κ.target.V × κ.target.V).2)) :
    Q (TripodFrame.markSource κ k).1.1 ↔ ¬ Q (centreSource κ).1.1 := by
  classical
  have hrow : ∀ a : NonDanglingEdge κ.data,
      a.stablePath = κ.ident.row.symm (legSlot p k) ↔ κ.ident.row a.stablePath = legSlot p k :=
    fun a ↦ Equiv.eq_symm_apply _
  have hCount := sum_ite_incidenceCount (data := κ.data) Q (κ.ident.row.symm (legSlot p k))
  have hCast := congrArg (fun m : ℕ ↦ (m : ZMod 2)) hCount
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hCast
  -- the edges: only `e` crosses
  have hRight : (∑ a : NonDanglingEdge κ.data,
      if a.stablePath = κ.ident.row.symm (legSlot p k) then
        ((if Q (a.1.1.1 : κ.target.V × κ.target.V).1 then (1 : ZMod 2) else 0) +
          (if Q (a.1.1.1 : κ.target.V × κ.target.V).2 then 1 else 0)) else 0) = 1 := by
    rw [Finset.sum_eq_single e]
    · rw [ite_eq_left ((hrow e).mpr he)]
      by_cases h1 : Q (e.1.1.1 : κ.target.V × κ.target.V).1 <;>
        by_cases h2 : Q (e.1.1.1 : κ.target.V × κ.target.V).2
      · exact absurd ⟨fun _ ↦ h2, fun _ ↦ h1⟩ hQe
      · simp [h1, h2]
      · simp [h1, h2]
      · exact absurd ⟨fun h ↦ absurd h h1, fun h ↦ absurd h h2⟩ hQe
    · intro a _ hae
      by_cases haL : a.stablePath = κ.ident.row.symm (legSlot p k)
      · rw [ite_eq_left haL]
        have hiff := hOther a ((hrow a).mp haL) hae
        by_cases h1 : Q (a.1.1.1 : κ.target.V × κ.target.V).1
        · have h2 := hiff.mp h1
          rw [ite_eq_left h1, ite_eq_left h2]
          decide
        · have h2 : ¬ Q (a.1.1.1 : κ.target.V × κ.target.V).2 := fun h ↦ h1 (hiff.mpr h)
          rw [ite_eq_right h1, ite_eq_right h2, add_zero]
      · rw [ite_eq_right haL]
    · intro h
      exact absurd (Finset.mem_univ e) h
  -- the vertices: only the centre and the mark count
  have hLeft : (∑ X : κ.data.SourceVertex,
      if Q X.1.1 then (incidenceCount κ.data X (κ.ident.row.symm (legSlot p k)) : ZMod 2)
        else 0) =
      (if Q (centreSource κ).1.1 then 1 else 0) +
        (if Q (TripodFrame.markSource κ k).1.1 then 1 else 0) := by
    have hPoint : ∀ X : κ.data.SourceVertex,
        (if Q X.1.1 then (incidenceCount κ.data X (κ.ident.row.symm (legSlot p k)) : ZMod 2)
          else 0) =
        (if X = centreSource κ then (if Q (centreSource κ).1.1 then 1 else 0) else 0) +
          (if X = TripodFrame.markSource κ k then
            (if Q (TripodFrame.markSource κ k).1.1 then 1 else 0) else 0) := by
      intro X
      rw [incidenceCount_leg κ k X]
      by_cases h1 : X = centreSource κ <;> by_cases h2 : X = TripodFrame.markSource κ k
      · subst h1
        by_cases hQ : Q (centreSource κ).1.1
        · simp [hQ, ← h2]
        · simp [hQ, ← h2]
      · subst h1
        simp [h2]
      · subst h2
        simp [h1]
      · simp [h1, h2]
    rw [Finset.sum_congr rfl fun X _ ↦ hPoint X, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp
  rw [hLeft, hRight] at hCast
  by_cases h1 : Q (centreSource κ).1.1 <;> by_cases h2 : Q (TripodFrame.markSource κ k).1.1
  · rw [ite_eq_left h1, ite_eq_left h2] at hCast
    exact absurd hCast (by decide)
  · exact ⟨fun h ↦ absurd h h2, fun h ↦ absurd h1 h⟩
  · exact ⟨fun _ ↦ h1, fun _ ↦ h2⟩
  · rw [ite_eq_right h1, ite_eq_right h2] at hCast
    exact absurd hCast (by decide)

end GadgetCut

/-! ## 6.  The parameter count (§4.8, read on the length matrix)

When the lost edges are three leaf edges `λ_j = [w_j, v_j]` and `φ(c) ∈ T̂`:

* each inner end `w_j` is trivalent, with `λ_j` its only lost edge (`exists_triEdges`): it lies
  in `T̂` because `φ(c)` does (`exists_not_isLost_at`), and a vertex of `G` over it with all its
  surviving edges over one edge would be ramified twice (`exists_second_not_isLost`);
* at a trivalent vertex of change zero with no mark over it, the two `T̂`-columns agree on every
  G-row (Pairing, §4.4: `matrix_eq_of_trivalent_of_noMark`), which the column trick forbids
  (`false_of_matrix_eq`: with the three lost columns they would be four columns of a nonsingular
  matrix supported on the three leg rows). So a mark lies over every `w_j`;
* the `w_j` are distinct, so every mark `k` lies over some `w_j`, and there the leg edge at the
  mark lies over `λ_j` (`legEdge_target_of_mark_over`, Part I `prop-local` r0-nd3).

This is the parameter count of §4.8 in its matrix form: no genericity, no long legs and no
positivity of the request are used, only nonsingularity and the local properties of Part I.
-/

/-! ### Local facts at one source vertex -/

section Local

variable {target : CFGraph.{0}} {deg : ℕ} {data : GluingDatum target deg}

/-- The index sum over the surviving edges at a vertex, in the `nonDanglingIncident` form of
`lem-rphi-nd`. -/
theorem sum_index_nonDanglingIncident (hNoGlue : DanglingEdgeNoGlue data)
    (X : data.SourceVertex) :
    (∑ g ∈ nonDanglingIncident data X, (data.sourceEdgeIndex g : ℤ)) =
      (nonDanglingValency data X : ℤ) - 2 +
        2 * ((data.vertexPartition X.1.1).blockCard X.1.2 : ℤ) -
        data.localRamification X.1.1 ⟨X.1.2, X.2⟩ := by
  classical
  have hForm := StableLocalProperties.localRamification_eq_nonDangling_form data hNoGlue X
  have hSum : (∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data X)).filter
        (fun edge ↦ ¬ IsDangling data edge.1), (data.sourceEdgeIndex edge.1 : ℤ)) =
      ∑ g ∈ nonDanglingIncident data X, (data.sourceEdgeIndex g : ℤ) := by
    refine Finset.sum_bij' (fun edge _ ↦ edge.1)
      (fun g hg ↦ ⟨g, ((mem_nonDanglingIncident data X g).mp hg).2⟩) ?_ ?_ ?_ ?_ ?_
    · intro edge hEdge
      exact (mem_nonDanglingIncident data X _).mpr ⟨(Finset.mem_filter.mp hEdge).2, edge.2⟩
    · intro g hg
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((mem_nonDanglingIncident data X g).mp hg).1⟩
    · intro edge _
      rfl
    · intro g _
      rfl
    · intro edge _
      rfl
  rw [← hSum, hForm]
  ring

/-- **Three surviving edges in two directions are too many** at a vertex of vanishing
ramification (`prop-local`, r0-nd3: the three edges lie over three distinct target edges). -/
theorem not_forall_target_mem_pair (hNoGlue : DanglingEdgeNoGlue data) {X : data.SourceVertex}
    (h3 : nonDanglingValency data X = 3)
    (hr : data.localRamification X.1.1 ⟨X.1.2, X.2⟩ = 0) (a b : target.edges) :
    ¬ ∀ g ∈ nonDanglingIncident data X, g.1.1 = a ∨ g.1.1 = b := by
  classical
  intro hAll
  have hCard : (nonDanglingIncident data X).card = 3 := by
    rw [card_nonDanglingIncident]; exact h3
  obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hCard
  have hSum := sum_index_nonDanglingIncident hNoGlue X
  rw [hset, Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton, h3] at hSum
  push_cast at hSum
  have hmem : ∀ g, g ∈ ({x, y, z} : Finset data.SourceEdge) → g ∈ nonDanglingIncident data X :=
    fun g hg ↦ hset ▸ hg
  have hxI := ((mem_nonDanglingIncident data X x).mp (hmem x (by simp))).2
  have hyI := ((mem_nonDanglingIncident data X y).mp (hmem y (by simp))).2
  have hzI := ((mem_nonDanglingIncident data X z).mp (hmem z (by simp))).2
  have hxM : data.sourceEdgeIndex x ≤ (data.vertexPartition X.1.1).blockCard X.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard data X ⟨x, hxI⟩
  have hyM : data.sourceEdgeIndex y ≤ (data.vertexPartition X.1.1).blockCard X.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard data X ⟨y, hyI⟩
  have hzM : data.sourceEdgeIndex z ≤ (data.vertexPartition X.1.1).blockCard X.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard data X ⟨z, hzI⟩
  have hxP := GluingDatum.sourceEdgeIndex_pos data x
  have hyP := GluingDatum.sourceEdgeIndex_pos data y
  have hzP := GluingDatum.sourceEdgeIndex_pos data z
  have hxt := hAll x (hmem x (by simp))
  have hyt := hAll y (hmem y (by simp))
  have hzt := hAll z (hmem z (by simp))
  have hPair : x.1.1 = y.1.1 ∨ x.1.1 = z.1.1 ∨ y.1.1 = z.1.1 := by
    rcases hxt with h1 | h1 <;> rcases hyt with h2 | h2 <;> rcases hzt with h4 | h4 <;>
      first
      | exact Or.inl (h1.trans h2.symm)
      | exact Or.inr (Or.inl (h1.trans h4.symm))
      | exact Or.inr (Or.inr (h2.trans h4.symm))
  rcases hPair with h | h | h
  · have := RowWalk.sourceEdgeIndex_add_le_blockCard data hxI hyI hxy h
    omega
  · have := RowWalk.sourceEdgeIndex_add_le_blockCard data hxI hzI hxz h
    omega
  · have := RowWalk.sourceEdgeIndex_add_le_blockCard data hyI hzI hyz h
    omega

/-- **Three surviving edges in one direction are too many** at a vertex of ramification at
most one. -/
theorem not_forall_target_eq (hNoGlue : DanglingEdgeNoGlue data) {X : data.SourceVertex}
    (h3 : nonDanglingValency data X = 3)
    (hr : data.localRamification X.1.1 ⟨X.1.2, X.2⟩ ≤ 1) (u : target.edges) :
    ¬ ∀ g ∈ nonDanglingIncident data X, g.1.1 = u := by
  classical
  intro hAll
  have hCard : (nonDanglingIncident data X).card = 3 := by
    rw [card_nonDanglingIncident]; exact h3
  obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hCard
  have hSum := sum_index_nonDanglingIncident hNoGlue X
  rw [hset, Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton, h3] at hSum
  push_cast at hSum
  have hmem : ∀ g, g ∈ ({x, y, z} : Finset data.SourceEdge) → g ∈ nonDanglingIncident data X :=
    fun g hg ↦ hset ▸ hg
  have hxI := ((mem_nonDanglingIncident data X x).mp (hmem x (by simp))).2
  have hyI := ((mem_nonDanglingIncident data X y).mp (hmem y (by simp))).2
  have hzI := ((mem_nonDanglingIncident data X z).mp (hmem z (by simp))).2
  have hxM : data.sourceEdgeIndex x ≤ (data.vertexPartition X.1.1).blockCard X.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard data X ⟨x, hxI⟩
  have hyM : data.sourceEdgeIndex y ≤ (data.vertexPartition X.1.1).blockCard X.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard data X ⟨y, hyI⟩
  have hzM : data.sourceEdgeIndex z ≤ (data.vertexPartition X.1.1).blockCard X.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard data X ⟨z, hzI⟩
  have hxP := GluingDatum.sourceEdgeIndex_pos data x
  have hyP := GluingDatum.sourceEdgeIndex_pos data y
  have hzP := GluingDatum.sourceEdgeIndex_pos data z
  have hxt := hAll x (hmem x (by simp))
  have hyt := hAll y (hmem y (by simp))
  have hzt := hAll z (hmem z (by simp))
  have h1 := RowWalk.sourceEdgeIndex_add_le_blockCard data hxI hyI hxy (hxt.trans hyt.symm)
  have h2 := RowWalk.sourceEdgeIndex_add_le_blockCard data hxI hzI hxz (hxt.trans hzt.symm)
  have h4 := RowWalk.sourceEdgeIndex_add_le_blockCard data hyI hzI hyz (hyt.trans hzt.symm)
  omega

end Local

/-! ### The end of a source edge over a target vertex, and its partner there -/

section Partner

variable {target : CFGraph.{0}} {deg : ℕ} (data : GluingDatum target deg)

/-- The end of the source edge `f` lying over the target vertex `w` (meaningful when `w` is an
end of the target edge of `f`). -/
def endOver (f : data.SourceEdge) (w : target.V) : data.SourceVertex :=
  if (data.sourceEnds f).1.1.1 = w then (data.sourceEnds f).1 else (data.sourceEnds f).2

theorem endOver_incident (f : data.SourceEdge) (w : target.V) :
    Incident data f (endOver data f w) := by
  unfold endOver
  split_ifs
  · exact incident_left data f
  · exact incident_right data f

theorem endOver_target {f : data.SourceEdge} {w : target.V}
    (h : f.1.1 ∈ GluingDatum.incidentEdges w) : (endOver data f w).1.1 = w := by
  unfold endOver
  split_ifs with h1
  · exact h1
  · rcases (Finset.mem_filter.mp h).2 with h2 | h2
    · exact absurd h2 h1
    · exact h2

theorem endOver_eq_of_incident {f : data.SourceEdge} {w : target.V} {X : data.SourceVertex}
    (hX : Incident data f X) (hXw : X.1.1 = w) : endOver data f w = X := by
  unfold endOver
  rcases hX with h | h
  · rw [ite_eq_left (by rw [h]; exact hXw)]
    exact h
  · by_cases h1 : (data.sourceEnds f).1.1.1 = w
    · exfalso
      have h2 : (data.sourceEnds f).2.1.1 = X.1.1 := congrArg (fun Y : data.SourceVertex ↦ Y.1.1) h
      exact TargetGeodesic.Dart.coe_fst_ne_snd (f.1.1 : target.edges)
        (h1.trans (hXw.symm.trans h2.symm))
    · rw [ite_eq_right h1]
      exact h

/-- **The partner of `f` at its end over `w`**: the other surviving edge there, when that end
has surviving valency two. -/
noncomputable def partner (f : data.SourceEdge) (w : target.V) : data.SourceEdge :=
  if h : nonDanglingValency data (endOver data f w) = 2 then stepEdge data h f else f

end Partner

/-! ### The gadget: which slots meet which branch vertices -/

section Slots

variable {n p degree : ℕ} {core : Core n p} {s : MarkSlots p}

/-- A surviving edge at a branch vertex lies on a slot ending there. -/
theorem end_of_incident_vertex {N P : ℕ} {C : Core N P} (κ : Frame C degree) (v : Fin N)
    (g : NonDanglingEdge κ.data) (hg : Incident κ.data g.1 (κ.ident.vertex.symm v).1) :
    C.tail (κ.ident.row g.stablePath) = v ∨ C.head (κ.ident.row g.stablePath) = v := by
  have hPos : 0 < incidenceCount κ.data (κ.ident.vertex.symm v).1 g.stablePath :=
    (incidenceCount_pos_iff _ _ _).mpr ⟨g, hg, rfl⟩
  have hInc := κ.ident.incidence (κ.ident.vertex.symm v) (κ.ident.row g.stablePath)
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at hInc
  rw [hInc] at hPos
  unfold coreIncidence at hPos
  by_cases h1 : C.tail (κ.ident.row g.stablePath) = v
  · exact Or.inl h1
  · by_cases h2 : C.head (κ.ident.row g.stablePath) = v
    · exact Or.inr h2
    · rw [ite_eq_right h1, ite_eq_right h2] at hPos
      omega

theorem isGSlot_or_eq_legSlot (j : Fin (p + 1 + 1 + 1 + 3)) :
    IsGSlot j ∨ ∃ k, j = legSlot p k := by
  by_cases h : j.val < p + 1 + 1 + 1
  · exact Or.inl h
  · right
    refine ⟨⟨j.val - (p + 1 + 1 + 1), by omega⟩, Fin.ext ?_⟩
    simp only [legSlot, Fin.val_natAdd]
    omega

theorem centre_ne_tripodMark (k : Fin 3) : centre n ≠ tripodMark n k := by
  intro h
  exact absurd h.symm (Fin.castSucc_lt_last _).ne

theorem tripodMark_injective : Function.Injective (tripodMark n) := fun _ _ h ↦
  markVertex_injective n (Fin.castSucc_injective _ h)

/-- **The centre meets only the legs.** -/
theorem not_isGSlot_of_incident_centre (κ : Frame (tripodCore core s) degree)
    (g : NonDanglingEdge κ.data) (hg : Incident κ.data g.1 (centreSource κ)) :
    ¬ IsGSlot (κ.ident.row g.stablePath) := by
  intro hG
  have hEnd := end_of_incident_vertex κ (centre n) g hg
  have hj : κ.ident.row g.stablePath = Fin.castAdd 3 ⟨(κ.ident.row g.stablePath).val, hG⟩ :=
    Fin.ext rfl
  rw [hj, tripodCore_tail_castAdd, tripodCore_head_castAdd] at hEnd
  rcases hEnd with h | h <;> exact absurd h (Fin.castSucc_lt_last _).ne

/-- **Mark `k` meets only G-slots and leg `k`.** -/
theorem isGSlot_or_eq_legSlot_of_incident_mark (κ : Frame (tripodCore core s) degree) (k : Fin 3)
    (g : NonDanglingEdge κ.data) (hg : Incident κ.data g.1 (TripodFrame.markSource κ k)) :
    IsGSlot (κ.ident.row g.stablePath) ∨ κ.ident.row g.stablePath = legSlot p k := by
  rcases isGSlot_or_eq_legSlot (κ.ident.row g.stablePath) with h | ⟨k', hk'⟩
  · exact Or.inl h
  · right
    have hEnd := end_of_incident_vertex κ (tripodMark n k) g hg
    rw [hk', tripodCore_tail_legSlot, tripodCore_head_legSlot] at hEnd
    rcases hEnd with h | h
    · exact absurd h (centre_ne_tripodMark k)
    · rw [hk', tripodMark_injective h]

/-- **Mark `k` carries exactly one surviving edge of leg `k`.** -/
theorem exists_legEdge_at_mark (κ : Frame (tripodCore core s) degree) (k : Fin 3) :
    ∃ ℓ : NonDanglingEdge κ.data, Incident κ.data ℓ.1 (TripodFrame.markSource κ k) ∧
      κ.ident.row ℓ.stablePath = legSlot p k := by
  obtain ⟨ℓ, hℓ, hrow⟩ := exists_incident_of_end κ (legSlot p k) (tripodMark n k)
    (Or.inr (tripodCore_head_legSlot k))
  exact ⟨ℓ, hℓ, by rw [hrow, Equiv.apply_symm_apply]⟩

theorem legEdge_unique_at_mark (κ : Frame (tripodCore core s) degree) (k : Fin 3)
    {g g' : NonDanglingEdge κ.data} (hg : Incident κ.data g.1 (TripodFrame.markSource κ k))
    (hg' : Incident κ.data g'.1 (TripodFrame.markSource κ k))
    (hr : κ.ident.row g.stablePath = legSlot p k) (hr' : κ.ident.row g'.stablePath = legSlot p k) :
    g = g' := by
  classical
  have hInc := κ.ident.incidence (κ.ident.vertex.symm (tripodMark n k)) (legSlot p k)
  rw [Equiv.apply_symm_apply] at hInc
  have hOne : incidenceCount κ.data (TripodFrame.markSource κ k)
      (κ.ident.row.symm (legSlot p k)) = 1 := by
    show incidenceCount κ.data (κ.ident.vertex.symm (tripodMark n k)).1 _ = 1
    rw [hInc]
    unfold coreIncidence
    rw [tripodCore_tail_legSlot, tripodCore_head_legSlot, ite_eq_right (centre_ne_tripodMark k),
      ite_eq_left rfl]
  unfold incidenceCount at hOne
  refine Finset.card_le_one.mp hOne.le g ?_ g' ?_
  · exact Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr hg,
      (Equiv.eq_symm_apply _).mpr hr⟩
  · exact Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr hg',
      (Equiv.eq_symm_apply _).mpr hr'⟩

/-- **A vertex other than the centre and the marks meets only G-slots**, once it meets one. -/
theorem isGSlot_of_incident_of_ne (κ : Frame (tripodCore core s) degree)
    {X : κ.data.SourceVertex} (hXc : X ≠ centreSource κ)
    (hXm : ∀ k, X ≠ TripodFrame.markSource κ k)
    {f : NonDanglingEdge κ.data} (hf : Incident κ.data f.1 X)
    (hfG : IsGSlot (κ.ident.row f.stablePath))
    {g : NonDanglingEdge κ.data} (hg : Incident κ.data g.1 X) :
    IsGSlot (κ.ident.row g.stablePath) := by
  rcases Nat.lt_or_ge (nonDanglingValency κ.data X) 3 with h | h
  · by_cases hgf : g = f
    · rw [hgf]
      exact hfG
    · have hval : nonDanglingValency κ.data X = 2 := by
        have h1 := NonDanglingValency.nonDanglingValency_ne_one κ.data κ.fullDim.connected X
        have hpos : 0 < nonDanglingValency κ.data X := by
          rw [← card_nonDanglingIncident]
          exact Finset.card_pos.mpr ⟨f.1, (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hf⟩⟩
        omega
      have hCons : Consecutive κ.data f g := ⟨fun h ↦ hgf h.symm, X, hf, hg, hval⟩
      rw [← stablePath_eq_of_consecutive hCons]
      exact hfG
  · let b : StableGraphIncidence.BranchVertex κ.data := ⟨X, h⟩
    rcases isGSlot_or_eq_legSlot (κ.ident.row g.stablePath) with hG | ⟨k, hk⟩
    · exact hG
    · exfalso
      have hg' : Incident κ.data g.1 (κ.ident.vertex.symm (κ.ident.vertex b)).1 := by
        rw [Equiv.symm_apply_apply]
        exact hg
      have hEnd := end_of_incident_vertex κ (κ.ident.vertex b) g hg'
      rw [hk, tripodCore_tail_legSlot, tripodCore_head_legSlot] at hEnd
      rcases hEnd with h1 | h1
      · apply hXc
        show X = (κ.ident.vertex.symm (centre n)).1
        rw [h1, Equiv.symm_apply_apply]
      · apply hXm k
        show X = (κ.ident.vertex.symm (tripodMark n k)).1
        rw [h1, Equiv.symm_apply_apply]

end Slots

/-! ### At a trivalent target vertex with one lost edge -/

section Trivalent

variable {n p degree : ℕ} {core : Core n p} {s : MarkSlots p}

/-- **`w` has exactly the three edges `l, a, b`**, pairwise distinct. -/
structure TriEdges {T : CFGraph} (w : T.V) (l a b : T.edges) : Prop where
  mem_iff : ∀ t, t ∈ GluingDatum.incidentEdges w ↔ t = l ∨ t = a ∨ t = b
  hab : a ≠ b
  hla : l ≠ a
  hlb : l ≠ b

theorem TriEdges.card {T : CFGraph} {w : T.V} {l a b : T.edges} (h : TriEdges w l a b) :
    (GluingDatum.incidentEdges w).card = 3 := by
  classical
  have hEq : GluingDatum.incidentEdges w = {l, a, b} := by
    ext t
    rw [h.mem_iff]
    simp
  rw [hEq]
  exact Finset.card_eq_three.mpr ⟨l, a, b, h.hla, h.hlb, h.hab, rfl⟩

theorem TriEdges.swap {T : CFGraph} {w : T.V} {l a b : T.edges} (h : TriEdges w l a b) :
    TriEdges w l b a :=
  ⟨fun t ↦ by rw [h.mem_iff]; tauto, h.hab.symm, h.hlb, h.hla⟩

/-- **Pairing at a trivalent vertex of change zero** (§4.4, Pairing; Part I `prop-local`
r0-nd2). Let `w` be a target vertex with edges `l, u, u'`, `l` lost, and no mark over `w`. A
G-edge `f` over `u` has its end over `w` of surviving valency two, and its partner there lies on
the same row, over `u'`, with the same index; the partner of the partner is `f`. -/
theorem partner_spec (κ : Frame (tripodCore core s) degree) {w : κ.target.V}
    {l u u' : κ.target.edges} (hw : TriEdges w l u u') (hl : IsLost κ l)
    (hNoMark : ∀ k, (TripodFrame.markSource κ k).1.1 ≠ w)
    (f : NonDanglingEdge κ.data) (hfG : IsGSlot (κ.ident.row f.stablePath)) (hfu : f.1.1.1 = u) :
    ∃ hS : ¬ IsDangling κ.data (partner κ.data f.1 w),
      NonDanglingEdge.stablePath (⟨partner κ.data f.1 w, hS⟩ : NonDanglingEdge κ.data) =
        f.stablePath ∧
      (partner κ.data f.1 w).1.1 = u' ∧
      κ.data.sourceEdgeIndex (partner κ.data f.1 w) = κ.data.sourceEdgeIndex f.1 ∧
      partner κ.data (partner κ.data f.1 w) w = f.1 := by
  classical
  have hNoGlue := κ.fullDim.danglingEdgeNoGlue
  set X := endOver κ.data f.1 w with hXdef
  have hfX : Incident κ.data f.1 X := endOver_incident κ.data f.1 w
  have hXw : X.1.1 = w :=
    endOver_target κ.data ((hw.mem_iff _).mpr (Or.inr (Or.inl hfu)))
  have hXc : X ≠ centreSource κ := fun h ↦
    not_isGSlot_of_incident_centre κ f (h ▸ hfX) hfG
  have hXm : ∀ k, X ≠ TripodFrame.markSource κ k := fun k h ↦ hNoMark k (h ▸ hXw)
  have hAllG : ∀ g : NonDanglingEdge κ.data, Incident κ.data g.1 X →
      IsGSlot (κ.ident.row g.stablePath) :=
    fun g hg ↦ isGSlot_of_incident_of_ne κ hXc hXm hfX hfG hg
  have hwX : TriEdges X.1.1 l u u' := hXw ▸ hw
  have hr0 : κ.data.localRamification X.1.1 ⟨X.1.2, X.2⟩ = 0 :=
    SlopesGeometric.localRamification_eq_zero_of_trivalent_target κ.data κ.fullDim.valid _
      (κ.fullDim.changeMinimal _) hwX.card _
  -- every surviving edge at `X` lies over `u` or `u'`
  have hDir : ∀ g ∈ nonDanglingIncident κ.data X, g.1.1 = u ∨ g.1.1 = u' := by
    intro g hg
    obtain ⟨gS, gI⟩ := (mem_nonDanglingIncident _ _ _).mp hg
    have hmem := (hwX.mem_iff _).mp ((incident_iff_target_mem_and_rel κ.data g X).mp gI).1
    rcases hmem with h | h | h
    · exact absurd h (hl ⟨g, gS⟩ (hAllG ⟨g, gS⟩ gI))
    · exact Or.inl h
    · exact Or.inr h
  -- so `X` has surviving valency two
  have h2 : nonDanglingValency κ.data X = 2 := by
    have h1 := NonDanglingValency.nonDanglingValency_ne_one κ.data κ.fullDim.connected X
    have hpos : 0 < nonDanglingValency κ.data X := by
      rw [← card_nonDanglingIncident]
      exact Finset.card_pos.mpr ⟨f.1, (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hfX⟩⟩
    have h3 := κ.fullDim.trivalent X
    have hne3 : nonDanglingValency κ.data X ≠ 3 := fun h ↦
      not_forall_target_mem_pair hNoGlue h hr0 u u' hDir
    omega
  -- the partner
  have hPartner : partner κ.data f.1 w = stepEdge κ.data h2 f.1 := by
    unfold partner
    rw [dite_eq_left h2]
  set g := stepEdge κ.data h2 f.1 with hgdef
  have gS : ¬ IsDangling κ.data g := stepEdge_not_dangling κ.data h2 f.1
  have gI : Incident κ.data g X := stepEdge_incident κ.data h2 f.1
  have hgf : g ≠ f.1 := stepEdge_ne κ.data h2 f.1
  have hCons : Consecutive κ.data f ⟨g, gS⟩ :=
    ⟨fun h ↦ hgf (congrArg Subtype.val h).symm, X, hfX, gI, h2⟩
  have hPath := stablePath_eq_of_consecutive hCons
  have hIdx := RowWalk.sourceEdgeIndex_eq_of_localRamification_eq_zero_of_noGlue hNoGlue h2 hr0
    f.2 hfX gS gI
  have hNeT := RowWalk.target_ne_of_localRamification_le_one hNoGlue h2 (by rw [hr0]; norm_num)
    f.2 hfX gS gI (Ne.symm hgf)
  have hgu' : g.1.1 = u' := by
    rcases hDir g ((mem_nonDanglingIncident _ _ _).mpr ⟨gS, gI⟩) with h | h
    · exact absurd (hfu.trans h.symm) hNeT
    · exact h
  -- the partner of the partner
  have hEnd : endOver κ.data g w = X := endOver_eq_of_incident κ.data gI hXw
  have h2' : nonDanglingValency κ.data (endOver κ.data g w) = 2 := by rw [hEnd]; exact h2
  have hBack : partner κ.data g w = f.1 := by
    unfold partner
    rw [dite_eq_left h2']
    rcases eq_or_eq_stepEdge κ.data h2' gS (by rw [hEnd]; exact gI) f.2
        (by rw [hEnd]; exact hfX) with h | h
    · exact absurd h.symm hgf
    · exact h.symm
  rw [hPartner]
  exact ⟨gS, hPath.symm, hgu', hIdx.symm, hBack⟩

/-- **The two columns at a trivalent vertex with no mark agree on the G-rows** (§4.4,
Pairing). -/
theorem matrix_eq_of_trivalent_of_noMark (κ : Frame (tripodCore core s) degree)
    {w : κ.target.V} {l a b : κ.target.edges} (hw : TriEdges w l a b)
    (hl : IsLost κ l) (hNoMark : ∀ k, (TripodFrame.markSource κ k).1.1 ≠ w)
    (r : Fin (p + 1 + 1 + 1 + 3)) (hr : IsGSlot (κ.slot r)) :
    κ.matrix r (κ.fullDim.labelling.targetEdge.symm a) =
      κ.matrix r (κ.fullDim.labelling.targetEdge.symm b) := by
  classical
  unfold Frame.matrix
  rw [LeafFibre.matrix_eq_sum_fibre, LeafFibre.matrix_eq_sum_fibre]
  have hw' : TriEdges w l b a := hw.swap
  -- the members of a row fibre are G-edges
  have hFib : ∀ {u : κ.target.edges} {f : κ.data.SourceEdge},
      f ∈ LeafFibre.rowFibre κ.fullDim.labelling r u →
      ∃ hS : ¬ IsDangling κ.data f,
        IsGSlot (κ.ident.row (NonDanglingEdge.stablePath (⟨f, hS⟩ : NonDanglingEdge κ.data))) ∧
        κ.fullDim.labelling.row (NonDanglingEdge.stablePath (⟨f, hS⟩ : NonDanglingEdge κ.data)) =
          r ∧
        f.1.1 = u := by
    intro u f hf
    obtain ⟨⟨hS, hrow⟩, ht⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hf
    refine ⟨hS, ?_, hrow, ht⟩
    have hEq : κ.ident.row (NonDanglingEdge.stablePath ⟨f, hS⟩) = κ.slot r :=
      (ident_row_eq_slot κ ⟨f, hS⟩).trans (congrArg κ.slot hrow)
    rw [hEq]
    exact hr
  have hTo : ∀ {u u' : κ.target.edges}, TriEdges w l u u' →
      ∀ f ∈ LeafFibre.rowFibre κ.fullDim.labelling r u,
      partner κ.data f w ∈ LeafFibre.rowFibre κ.fullDim.labelling r u' ∧
        partner κ.data (partner κ.data f w) w = f ∧
        κ.data.sourceEdgeIndex (partner κ.data f w) = κ.data.sourceEdgeIndex f := by
    intro u u' hwu f hf
    obtain ⟨hS, hG, hrow, ht⟩ := hFib hf
    obtain ⟨hS', hPath, ht', hIdx, hBack⟩ := partner_spec κ hwu hl hNoMark ⟨f, hS⟩ hG ht
    refine ⟨(LeafFibre.mem_rowFibre _ _ _ _).mpr ⟨⟨hS', ?_⟩, ht'⟩, hBack, hIdx⟩
    rw [hPath]
    exact hrow
  refine Finset.sum_nbij' (fun f ↦ partner κ.data f w) (fun f ↦ partner κ.data f w)
    (fun f hf ↦ (hTo hw f hf).1) (fun f hf ↦ (hTo hw' f hf).1)
    (fun f hf ↦ (hTo hw f hf).2.1) (fun f hf ↦ (hTo hw' f hf).2.1) ?_
  intro f hf
  rw [(hTo hw f hf).2.2]

/-- **The column trick** (§4.4, with the span property of Lemma 4.5). If the columns of two target
edges `a ≠ b`, `a` not lost, agree on every G-row, then the column of `a` minus that of `b` and
the three lost columns are four columns of a nonsingular matrix supported on the three leg rows.
-/
theorem false_of_matrix_eq (κ : Frame (tripodCore core s) degree)
    (lam : Fin 3 → κ.target.edges) (hInj : Function.Injective lam)
    (hLam : ∀ j, IsLost κ (lam j)) {a b : κ.target.edges} (ha : ∀ j, a ≠ lam j) (hab : a ≠ b)
    (h : ∀ r, IsGSlot (κ.slot r) → κ.matrix r (κ.fullDim.labelling.targetEdge.symm a) =
      κ.matrix r (κ.fullDim.labelling.targetEdge.symm b)) : False := by
  classical
  set E := κ.fullDim.labelling.targetEdge
  have hcab : E.symm a ≠ E.symm b := fun h' ↦ hab (E.symm.injective h')
  set M' := κ.matrix.updateCol (E.symm a)
    (fun r ↦ κ.matrix r (E.symm a) + (-1 : ℚ) • κ.matrix r (E.symm b)) with hM'
  have hdet : M'.det ≠ 0 := by
    rw [hM', Matrix.det_updateCol_add_smul_self _ hcab]
    exact κ.det_ne_zero
  let C : Finset (Fin (p + 1 + 1 + 1 + 3)) :=
    insert (E.symm a) ((Finset.univ : Finset (Fin 3)).image fun j ↦ E.symm (lam j))
  have hnot : E.symm a ∉ (Finset.univ : Finset (Fin 3)).image fun j ↦ E.symm (lam j) := by
    intro hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
    exact ha j (E.symm.injective hj.symm)
  have hC : C.card = 4 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _
      (show Function.Injective (fun j ↦ E.symm (lam j)) from E.symm.injective.comp hInj)]
    simp
  have hLe := card_le_of_cols_supported M' hdet C
    ((Finset.univ : Finset (Fin (p + 1 + 1 + 1 + 3))).filter fun r ↦ ¬ IsGSlot (κ.slot r))
    (by
      intro c hc r hr
      have hG : IsGSlot (κ.slot r) := by
        by_contra hG
        exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩)
      rcases Finset.mem_insert.mp hc with rfl | hc
      · rw [hM', Matrix.updateCol_self, h r hG]
        ring
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hc
        have hne : E.symm (lam j) ≠ E.symm a := fun h' ↦ ha j (E.symm.injective h').symm
        rw [hM', Matrix.updateCol_ne hne]
        exact matrix_eq_zero_of_isLost κ (hLam j) r hG)
  have h3 := card_legRows_le κ
  omega

/-- **At a mark over a trivalent vertex with a lost edge, the leg leaves up the lost edge**
(§4.8 and Part I `prop-local` r0-nd3: the three edges at the mark lie over the three edges
at `w`, and the two G-edges cannot lie over the lost one). -/
theorem legEdge_target_of_mark_over (κ : Frame (tripodCore core s) degree) {w : κ.target.V}
    {l a b : κ.target.edges} (hw : TriEdges w l a b) (hl : IsLost κ l) (k : Fin 3)
    (hk : (TripodFrame.markSource κ k).1.1 = w) (ℓ : NonDanglingEdge κ.data)
    (hℓ : Incident κ.data ℓ.1 (TripodFrame.markSource κ k))
    (hℓr : κ.ident.row ℓ.stablePath = legSlot p k) : ℓ.1.1.1 = l := by
  classical
  by_contra hne
  set X := TripodFrame.markSource κ k
  have hwX : TriEdges X.1.1 l a b := hk ▸ hw
  have h3 : nonDanglingValency κ.data X = 3 :=
    le_antisymm (κ.fullDim.trivalent X) (three_le_markSource κ k)
  have hr0 : κ.data.localRamification X.1.1 ⟨X.1.2, X.2⟩ = 0 :=
    SlopesGeometric.localRamification_eq_zero_of_trivalent_target κ.data κ.fullDim.valid _
      (κ.fullDim.changeMinimal _) hwX.card _
  apply not_forall_target_mem_pair κ.fullDim.danglingEdgeNoGlue h3 hr0 a b
  intro g hg
  obtain ⟨gS, gI⟩ := (mem_nonDanglingIncident _ _ _).mp hg
  have hmem := (hwX.mem_iff _).mp ((incident_iff_target_mem_and_rel κ.data g X).mp gI).1
  have hgl : g.1.1 ≠ l := by
    rcases isGSlot_or_eq_legSlot_of_incident_mark κ k ⟨g, gS⟩ gI with hG | hL
    · exact hl ⟨g, gS⟩ hG
    · have := legEdge_unique_at_mark κ k gI hℓ hL hℓr
      rw [show g = ℓ.1 from congrArg Subtype.val this]
      exact hne
  rcases hmem with h | h | h
  · exact absurd h hgl
  · exact Or.inl h
  · exact Or.inr h

end Trivalent

/-! ### The inner end of a lost leaf edge is trivalent, with two edges in `T̂` -/

section InnerEnd

/-- **A star with leaf tips is the whole graph.** In a connected graph, if every edge at `w` has
a leaf at its far end, every vertex is an end of an edge at `w`. -/
theorem exists_incident_of_star {T : CFGraph} (hConn : graph_connected T) {w : T.V}
    (hne : (GluingDatum.incidentEdges w).Nonempty)
    (hLeaves : ∀ t ∈ GluingDatum.incidentEdges w, ∀ x : T.V,
      ((t : T.V × T.V).1 = x ∨ (t : T.V × T.V).2 = x) → x ≠ w → IsLeafVertex T x)
    (z : T.V) :
    ∃ t ∈ GluingDatum.incidentEdges w, (t : T.V × T.V).1 = z ∨ (t : T.V × T.V).2 = z := by
  classical
  by_contra hz
  let S : Finset T.V := Finset.univ.filter fun x ↦
    ∃ t ∈ GluingDatum.incidentEdges w, (t : T.V × T.V).1 = x ∨ (t : T.V × T.V).2 = x
  have hmem : ∀ x, x ∈ S ↔
      ∃ t ∈ GluingDatum.incidentEdges w, (t : T.V × T.V).1 = x ∨ (t : T.V × T.V).2 = x := by
    intro x
    simp [S]
  obtain ⟨t₀, ht₀⟩ := hne
  have hwS : w ∈ S := (hmem w).mpr ⟨t₀, ht₀, (Finset.mem_filter.mp ht₀).2⟩
  obtain ⟨v, hv, y, hy, hvy⟩ := hConn S ⟨w, z, hwS, fun h ↦ hz ((hmem z).mp h)⟩
  unfold num_edges at hvy
  obtain ⟨e, he⟩ := Multiset.card_pos_iff_exists_mem.mp hvy
  obtain ⟨heT, hev⟩ := Multiset.mem_filter.mp he
  let t' : T.edges := ⟨e, ⟨0, Multiset.count_pos.mpr heT⟩⟩
  have hends : ((t' : T.V × T.V).1 = v ∨ (t' : T.V × T.V).2 = v) ∧
      ((t' : T.V × T.V).1 = y ∨ (t' : T.V × T.V).2 = y) := by
    rcases hev with rfl | rfl
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩
  apply hy
  obtain ⟨t, ht, htv⟩ := (hmem v).mp hv
  by_cases hvw : v = w
  · subst hvw
    exact (hmem y).mpr ⟨t', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hends.1⟩, hends.2⟩
  · have hleaf := hLeaves t ht v htv hvw
    have ht'eq : t' = t :=
      Finset.card_le_one.mp hleaf.le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hends.1⟩) _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htv⟩)
    exact (hmem y).mpr ⟨t, ht, ht'eq ▸ hends.2⟩

/-- The far end of a leaf edge at a vertex that is not a leaf is a leaf. -/
theorem isLeafVertex_of_isLeafEdge {T : CFGraph} {t : T.edges} (ht : IsLeafEdge T t) {x y : T.V}
    (hx : (t : T.V × T.V).1 = x ∨ (t : T.V × T.V).2 = x) (hxl : ¬ IsLeafVertex T x)
    (hy : (t : T.V × T.V).1 = y ∨ (t : T.V × T.V).2 = y) (hyx : y ≠ x) : IsLeafVertex T y := by
  rcases ht with h | h <;> rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hyx
  · exact absurd (isLeafVertex_of_vertex_degree h) hxl
  · exact isLeafVertex_of_vertex_degree h
  · exact absurd rfl hyx
  · exact absurd rfl hyx
  · exact isLeafVertex_of_vertex_degree h
  · exact absurd (isLeafVertex_of_vertex_degree h) hxl
  · exact absurd rfl hyx

variable {n p degree : ℕ} {core : Core n p} {s : MarkSlots p}

/-- The end of a leaf edge that is not a leaf (Lemma 4.2(ii): `w` in `t_v = [w, v]`). No
target edge of a full-dimensional morphism joins two leaves. -/
theorem exists_inner_end (κ : Frame (tripodCore core s) degree) {t : κ.target.edges}
    (ht : IsLeafEdge κ.target t) :
    ∃ w : κ.target.V, ((t : κ.target.V × κ.target.V).1 = w ∨
      (t : κ.target.V × κ.target.V).2 = w) ∧ ¬ IsLeafVertex κ.target w := by
  have hNL := noLeafToLeafEdge_of_fullDimensional κ.fullDim
  rcases ht with h | h
  · exact ⟨_, Or.inr rfl, hNL t (isLeafVertex_of_vertex_degree h)⟩
  · exact ⟨_, Or.inl rfl, fun h1 ↦ hNL t h1 (isLeafVertex_of_vertex_degree h)⟩

/-- **The inner end of a lost edge lies in `T̂`** when `φ(c)` does: otherwise every edge there is
lost, hence a leaf edge, the target is the star at that vertex, and `φ(c)` would be on it. -/
theorem exists_not_isLost_at (κ : Frame (tripodCore core s) degree)
    (hc : TripodFrame.centreTarget κ ∈ TripodFrame.gImage κ)
    (hLeafLost : ∀ t, IsLost κ t → IsLeafEdge κ.target t)
    {w : κ.target.V} (hwl : ¬ IsLeafVertex κ.target w)
    (hne : (GluingDatum.incidentEdges w).Nonempty) :
    ∃ u ∈ GluingDatum.incidentEdges w, ¬ IsLost κ u := by
  by_contra hNo
  have hAll : ∀ u ∈ GluingDatum.incidentEdges w, IsLost κ u := fun u hu ↦ by
    by_contra h
    exact hNo ⟨u, hu, h⟩
  have hTip : ∀ t ∈ GluingDatum.incidentEdges w, ∀ x : κ.target.V,
      ((t : κ.target.V × κ.target.V).1 = x ∨ (t : κ.target.V × κ.target.V).2 = x) → x ≠ w →
      IsLeafVertex κ.target x := fun t ht x hx hxw ↦
    isLeafVertex_of_isLeafEdge (hLeafLost t (hAll t ht)) (Finset.mem_filter.mp ht).2 hwl hx hxw
  obtain ⟨t, ht, hct⟩ :=
    exists_incident_of_star κ.fullDim.targetConnected hne hTip (TripodFrame.centreTarget κ)
  obtain ⟨g, hG, hg⟩ := hc
  have hLostG : IsLost κ g.1.1.1 := by
    by_cases hcw : TripodFrame.centreTarget κ = w
    · exact hAll _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcw ▸ hg⟩)
    · have hleaf := hTip t ht _ hct hcw
      have hgt : g.1.1.1 = t :=
        Finset.card_le_one.mp hleaf.le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩) _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hct⟩)
      rw [hgt]
      exact hAll t ht
  exact hLostG g hG rfl

/-- **The inner end has a second edge in `T̂`** (§4.8 and Part I `prop-local`). Take a G-edge
over an edge `u` of `T̂` at `w` and its end `X` over `w`, where the ramification is at most one.
If every surviving edge at `X` lay over `u`, `X` would be ramified at least twice. At a mark, the
two G-edges over `u` force the leg edge onto a lost leaf edge, of index one, and then `X` is
ramified at least `|X| ≥ 2` times or the two G-edges cannot both fit in one sheet. -/
theorem exists_second_not_isLost (κ : Frame (tripodCore core s) degree)
    (hLeafLost : ∀ t, IsLost κ t → IsLeafEdge κ.target t)
    {w : κ.target.V} (hwl : ¬ IsLeafVertex κ.target w) {u : κ.target.edges}
    (hu : u ∈ GluingDatum.incidentEdges w) (hul : ¬ IsLost κ u) :
    ∃ u' ∈ GluingDatum.incidentEdges w, u' ≠ u ∧ ¬ IsLost κ u' := by
  classical
  have hNoGlue := κ.fullDim.danglingEdgeNoGlue
  -- a G-edge over `u`, and its end over `w`
  obtain ⟨f, hfG, hfu⟩ : ∃ f : NonDanglingEdge κ.data,
      IsGSlot (κ.ident.row f.stablePath) ∧ f.1.1.1 = u := by
    by_contra h
    exact hul fun f hG hfu ↦ h ⟨f, hG, hfu⟩
  set X := endOver κ.data f.1 w with hXdef
  have hfX : Incident κ.data f.1 X := endOver_incident κ.data f.1 w
  have hXw : X.1.1 = w := endOver_target κ.data (hfu ▸ hu)
  have hXc : X ≠ centreSource κ := fun h ↦ not_isGSlot_of_incident_centre κ f (h ▸ hfX) hfG
  have hcard : 2 ≤ (GluingDatum.incidentEdges X.1.1).card := by
    rw [hXw]
    have h1 : (GluingDatum.incidentEdges w).card ≠ 1 := hwl
    have h0 : 0 < (GluingDatum.incidentEdges w).card := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  have hr1 : κ.data.localRamification X.1.1 ⟨X.1.2, X.2⟩ ≤ 1 :=
    DivalentSourceLocal.localRamification_le_one_of_nonleaf κ.data κ.fullDim.valid X
      (κ.fullDim.changeMinimal _) hcard
  -- a G-edge at `X` over another edge answers
  have hGood : ∀ g : NonDanglingEdge κ.data, Incident κ.data g.1 X →
      IsGSlot (κ.ident.row g.stablePath) → g.1.1.1 ≠ u →
      ∃ u' ∈ GluingDatum.incidentEdges w, u' ≠ u ∧ ¬ IsLost κ u' := by
    intro g hgX hgG hgu
    refine ⟨g.1.1.1, ?_, hgu, fun hL ↦ hL g hgG rfl⟩
    have := ((incident_iff_target_mem_and_rel κ.data g.1 X).mp hgX).1
    rwa [hXw] at this
  have hpos : 0 < nonDanglingValency κ.data X := by
    rw [← card_nonDanglingIncident]
    exact Finset.card_pos.mpr ⟨f.1, (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hfX⟩⟩
  have h1 := NonDanglingValency.nonDanglingValency_ne_one κ.data κ.fullDim.connected X
  have hle3 := κ.fullDim.trivalent X
  -- at valency three some surviving edge lies over another edge
  have hOther3 : nonDanglingValency κ.data X = 3 →
      ∃ g : NonDanglingEdge κ.data, Incident κ.data g.1 X ∧ g.1.1.1 ≠ u := by
    intro h3
    by_contra hNo
    apply not_forall_target_eq hNoGlue h3 hr1 u
    intro g hg
    obtain ⟨gS, gI⟩ := (mem_nonDanglingIncident _ _ _).mp hg
    by_contra hgu
    exact hNo ⟨⟨g, gS⟩, gI, hgu⟩
  by_cases hXm : ∃ k, X = TripodFrame.markSource κ k
  · -- `X` is a mark
    obtain ⟨k, hk⟩ := hXm
    have h3 : nonDanglingValency κ.data X = 3 := by
      rw [hk]
      exact le_antisymm (κ.fullDim.trivalent _) (three_le_markSource κ k)
    obtain ⟨ℓ, hℓX, hℓr⟩ := exists_legEdge_at_mark κ k
    have hℓX' : Incident κ.data ℓ.1 X := by rw [hk]; exact hℓX
    have hℓf : ℓ.1 ≠ f.1 := by
      intro h
      have hEq : ℓ = f := Subtype.ext h
      rw [hEq] at hℓr
      exact legSlot_not_isGSlot k (hℓr ▸ hfG)
    -- the third surviving edge at the mark, a G-edge
    have hfmem : f.1 ∈ nonDanglingIncident κ.data X :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hfX⟩
    have hℓmem : ℓ.1 ∈ nonDanglingIncident κ.data X :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨ℓ.2, hℓX'⟩
    have hcardE : (((nonDanglingIncident κ.data X).erase f.1).erase ℓ.1).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hℓf, hℓmem⟩),
        Finset.card_erase_of_mem hfmem, card_nonDanglingIncident, h3]
    obtain ⟨g2, hg2⟩ := Finset.card_eq_one.mp hcardE
    have hg2mem : g2 ∈ ((nonDanglingIncident κ.data X).erase f.1).erase ℓ.1 := by
      rw [hg2]
      exact Finset.mem_singleton_self _
    obtain ⟨hg2ℓ, hg2'⟩ := Finset.mem_erase.mp hg2mem
    obtain ⟨hg2f, hg2''⟩ := Finset.mem_erase.mp hg2'
    obtain ⟨g2S, g2I⟩ := (mem_nonDanglingIncident _ _ _).mp hg2''
    have g2I' : Incident κ.data g2 (TripodFrame.markSource κ k) := by rw [← hk]; exact g2I
    have hg2G : IsGSlot (κ.ident.row (NonDanglingEdge.stablePath ⟨g2, g2S⟩)) := by
      rcases isGSlot_or_eq_legSlot_of_incident_mark κ k ⟨g2, g2S⟩ g2I' with h | h
      · exact h
      · exact absurd (congrArg Subtype.val (legEdge_unique_at_mark κ k g2I' hℓX h hℓr)) hg2ℓ
    by_cases hg2u : g2.1.1 = u
    · -- both G-edges lie over `u`, so the leg edge lies over another edge
      have hfg2 : f.1 ≠ g2 := Ne.symm hg2f
      have hSet : nonDanglingIncident κ.data X = {f.1, g2, ℓ.1} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact hfmem
          · exact hg2''
          · exact hℓmem
        · rw [card_nonDanglingIncident, h3]
          exact (Finset.card_eq_three.mpr ⟨f.1, g2, ℓ.1, hfg2, Ne.symm hℓf, hg2ℓ, rfl⟩).ge
      have hℓu : ℓ.1.1.1 ≠ u := by
        intro hℓu
        apply not_forall_target_eq hNoGlue h3 hr1 u
        intro x hx
        rw [hSet] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfu
        · exact hg2u
        · exact hℓu
      by_cases hℓL : IsLost κ ℓ.1.1.1
      · exfalso
        obtain ⟨v, hv, hvℓ⟩ := exists_leaf_of_isLeafEdge (hLeafLost _ hℓL)
        have hℓ1 : κ.data.sourceEdgeIndex ℓ.1 = 1 :=
          LeafFibre.sourceEdgeIndex_eq_one_above_leaf κ.fullDim hv hvℓ
        have hSum := sum_index_nonDanglingIncident hNoGlue X
        rw [hSet, Finset.sum_insert (by simp [hfg2, Ne.symm hℓf]),
          Finset.sum_insert (by simp [hg2ℓ]), Finset.sum_singleton, h3] at hSum
        push_cast at hSum
        have hPair := RowWalk.sourceEdgeIndex_add_le_blockCard κ.data hfX g2I hfg2
          (hfu.trans hg2u.symm)
        have hfP := GluingDatum.sourceEdgeIndex_pos κ.data f.1
        have hg2P := GluingDatum.sourceEdgeIndex_pos κ.data g2
        omega
      · refine ⟨ℓ.1.1.1, ?_, hℓu, hℓL⟩
        have := ((incident_iff_target_mem_and_rel κ.data ℓ.1 X).mp hℓX').1
        rwa [hXw] at this
    · exact hGood ⟨g2, g2S⟩ g2I hg2G hg2u
  · -- `X` is a vertex of `G`: every surviving edge at it is a G-edge
    have hXm' : ∀ k, X ≠ TripodFrame.markSource κ k := fun k h ↦ hXm ⟨k, h⟩
    have hAllG : ∀ g : NonDanglingEdge κ.data, Incident κ.data g.1 X →
        IsGSlot (κ.ident.row g.stablePath) :=
      fun g hg ↦ isGSlot_of_incident_of_ne κ hXc hXm' hfX hfG hg
    rcases Nat.lt_or_ge (nonDanglingValency κ.data X) 3 with hlt | hge
    · have h2 : nonDanglingValency κ.data X = 2 := by omega
      have gS := stepEdge_not_dangling κ.data h2 f.1
      have gI := stepEdge_incident κ.data h2 f.1
      have hgf := stepEdge_ne κ.data h2 f.1
      have hNeT := RowWalk.target_ne_of_localRamification_le_one hNoGlue h2 hr1 f.2 hfX gS gI
        (Ne.symm hgf)
      exact hGood ⟨_, gS⟩ gI (hAllG ⟨_, gS⟩ gI) (fun h ↦ hNeT (hfu.trans h.symm))
    · obtain ⟨g, hgX, hgu⟩ := hOther3 (by omega)
      exact hGood g hgX (hAllG g hgX) hgu

/-- **The inner end of a lost leaf edge** (§4.8, read on the frame): when the lost
edges are leaf edges and `φ(c) ∈ T̂`, the end `w` of a lost edge `t` that is not a leaf has
exactly three edges, `t` and two edges of `T̂`. -/
theorem exists_triEdges (κ : Frame (tripodCore core s) degree)
    (hc : TripodFrame.centreTarget κ ∈ TripodFrame.gImage κ)
    (hLeafLost : ∀ t, IsLost κ t → IsLeafEdge κ.target t) {t : κ.target.edges}
    (htl : IsLost κ t) :
    ∃ (w : κ.target.V) (u u' : κ.target.edges),
      ((t : κ.target.V × κ.target.V).1 = w ∨ (t : κ.target.V × κ.target.V).2 = w) ∧
      TriEdges w t u u' ∧ ¬ IsLost κ u ∧ ¬ IsLost κ u' := by
  classical
  obtain ⟨w, htw, hwl⟩ := exists_inner_end κ (hLeafLost t htl)
  have htmem : t ∈ GluingDatum.incidentEdges w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, htw⟩
  obtain ⟨u, hu, hul⟩ := exists_not_isLost_at κ hc hLeafLost hwl ⟨t, htmem⟩
  obtain ⟨u', hu', hu'u, hu'l⟩ := exists_second_not_isLost κ hLeafLost hwl hu hul
  have htu : t ≠ u := fun h ↦ hul (h ▸ htl)
  have htu' : t ≠ u' := fun h ↦ hu'l (h ▸ htl)
  have hle := κ.data.incidentEdges_card_le_three_of_changeMinimalAt κ.fullDim.valid w
    (κ.fullDim.changeMinimal w)
  have hSet : GluingDatum.incidentEdges w = {t, u, u'} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact htmem
      · exact hu
      · exact hu'
    · rw [Finset.card_eq_three.mpr ⟨t, u, u', htu, htu', hu'u.symm, rfl⟩]
      exact hle
  refine ⟨w, u, u', htw, ⟨fun x ↦ ?_, hu'u.symm, htu, htu'⟩, hul, hu'l⟩
  rw [hSet]
  simp

end InnerEnd

/-! ## 7.  Not claw ⇒ glued (Theorem 4.7(a), §4.8) -/

section Glued

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p}

/-- Leg `k` has a **leaf detour** (Lemma 4.2(ii)): some edge of the leg lies over a leaf edge
of the target. -/
def HasDetour {degree : ℕ} (κ : Frame (tripodCore core s) degree) (k : Fin 3) : Prop :=
  ∃ e : NonDanglingEdge κ.data, κ.ident.row e.stablePath = legSlot p k ∧
    IsLeafEdge κ.target e.1.1.1

/-- **Leg shape, no detour** (Lemma 4.2(i)). A leg with no leaf detour passes over each target
edge at most once. -/
theorem legEdge_injective_of_noDetour {degree : ℕ}
    (κ : Frame (tripodCore core s) degree) (k : Fin 3) (hNo : ¬ HasDetour κ k)
    (e e' : NonDanglingEdge κ.data) (he : κ.ident.row e.stablePath = legSlot p k)
    (he' : κ.ident.row e'.stablePath = legSlot p k) (hT : e.1.1.1 = e'.1.1.1) : e = e' := by
  -- the leg row avoids the leaves: an edge over an edge at a leaf would be a detour
  have hAvoid : RowWalk.RowAvoidsLeaves κ.data (κ.ident.row.symm (legSlot p k)) := by
    intro edge hOn v hv hMem
    obtain ⟨hS, hPath⟩ := hOn
    apply hNo
    refine ⟨⟨edge, hS⟩, (congrArg κ.ident.row hPath).trans (Equiv.apply_symm_apply _ _), ?_⟩
    have hDeg : vertex_degree κ.target v = 1 := by
      have := card_incidentEdges_eq_vertex_degree κ.target v
      unfold IsLeafVertex at hv
      omega
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hMem
    rcases hMem with h | h
    · exact Or.inl (h ▸ hDeg)
    · exact Or.inr (h ▸ hDeg)
  -- so it has ramification at most one, and its walk in the tree `T` is a geodesic
  have hInj := RowGeodesic.rowTargetInjective_of_genusZero κ.fullDim.targetConnected
    κ.fullDim.targetGenus κ.fullDim.danglingEdgeNoGlue κ.fullDim.pathEnds
    (RowWalk.rowRamificationAtMostOne_of_rowAvoidsLeaves κ.fullDim hAvoid)
  have hOn : ∀ m : NonDanglingEdge κ.data, κ.ident.row m.stablePath = legSlot p k →
      RowWalk.OnRow κ.data (κ.ident.row.symm (legSlot p k)) m.1 := by
    intro m hm
    refine ⟨m.2, ?_⟩
    show m.stablePath = _
    rw [← hm, Equiv.symm_apply_apply]
  exact Subtype.ext (hInj e.1 e'.1 (hOn e he) (hOn e' he') hT)

-- Cubicity of `G̃` is not used here, only its connectedness; `hcubic` stays in the statement.
set_option linter.unusedVariables false in
/-- **A leg without detour stays in `φ(G)` when `φ(c) ∈ φ(G)`** (Lemma 4.2(i) and the proof of
Theorem 4.7(a)). Its image is the geodesic `[φ(k), φ(c)]` of `T`, and `T̂ = φ(G)` is a subtree
containing both ends. This is the one place where the connectedness of `G̃` is used.

Proof (section 5 above): if the leg crossed a lost edge `t`, cut `T` at `t`. No G-edge crosses the
cut, so `φ(k)` and `φ(c)`, both in `T̂`, are on one side of it (`iff_of_mem_gImage`); but the leg crosses
it exactly once (`legEdge_injective_of_noDetour`), so its two ends are on opposite sides
(`markSource_iff_not_centreSource`). -/
theorem legEdge_not_isLost_of_noDetour (hcubic : core.Cubic) (hconn : core.Connected)
    (κ : Frame (tripodCore core s) (3 + 2)) (k : Fin 3) (hNo : ¬ HasDetour κ k)
    (hc : TripodFrame.centreTarget κ ∈ TripodFrame.gImage κ)
    (e : NonDanglingEdge κ.data) (he : κ.ident.row e.stablePath = legSlot p k) :
    ¬ IsLost κ e.1.1.1 := by
  intro hLost
  -- cut the tree `T` at the lost edge `t`
  obtain ⟨A⟩ := TargetGeodesic.exists_treeRank κ.target κ.fullDim.targetConnected
    κ.fullDim.targetGenus
  let Q : κ.target.V → Prop := Below A e.1.1.1
  -- no G-edge crosses the cut, so `φ(k)` and `φ(c)` are on one side of it
  have hG : ∀ a : NonDanglingEdge κ.data, IsGSlot (κ.ident.row a.stablePath) →
      (Q (a.1.1.1 : κ.target.V × κ.target.V).1 ↔ Q (a.1.1.1 : κ.target.V × κ.target.V).2) :=
    fun a ha ↦ (below_fst_iff_snd A _ _).mpr (hLost a ha)
  have hSide : Q (TripodFrame.markSource κ k).1.1 ↔ Q (centreSource κ).1.1 :=
    iff_of_mem_gImage hconn κ hG (markTarget_mem_gImage κ k) hc
  -- leg `k` crosses it exactly once (Lemma 4.2(i)), so its two ends are on opposite sides
  have hLeg := markSource_iff_not_centreSource κ k Q e he
    (fun h ↦ (below_fst_iff_snd A _ _).mp h rfl)
    (fun a ha hae ↦ (below_fst_iff_snd A _ _).mpr fun hT ↦
      hae (legEdge_injective_of_noDetour κ k hNo a e ha he hT))
  by_cases h : Q (centreSource κ).1.1
  · exact hLeg.mp (hSide.mpr h) h
  · exact h (hSide.mp (hLeg.mpr h))

/-- **Long legs leave `φ(G)`** (Lemma 4.6). A leg that passes over each target edge at
most once, and only over edges of `φ(G)`, has length at most `4 L(G)`, where `4 = deg φ - 1`. -/
theorem legLength_le_of_noDetour (κ : Frame (tripodCore core s) (3 + 2))
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hz : ∀ i, 0 ≤ κ.coordsAt y i) (k : Fin 3)
    (hInj : ∀ e e' : NonDanglingEdge κ.data, κ.ident.row e.stablePath = legSlot p k →
      κ.ident.row e'.stablePath = legSlot p k → e.1.1.1 = e'.1.1.1 → e = e')
    (hNotLost : ∀ e : NonDanglingEdge κ.data, κ.ident.row e.stablePath = legSlot p k →
      ¬ IsLost κ e.1.1.1) :
    legLength y k ≤ 4 * ∑ i, baseRequest s y i := by
  classical
  set L := κ.fullDim.labelling
  set z := κ.coordsAt y
  -- the entries, as fibre sums, and their sign
  have hEntry : ∀ r c, κ.matrix r c =
      ∑ e ∈ LeafFibre.rowFibre L r (L.targetEdge c), (1 : ℚ) / κ.data.sourceEdgeIndex e := by
    intro r c
    have := LeafFibre.matrix_eq_sum_fibre L r (L.targetEdge c)
    rw [Equiv.symm_apply_apply] at this
    exact this
  have hM : ∀ r c, 0 ≤ κ.matrix r c := fun r c ↦ by
    rw [hEntry]
    exact Finset.sum_nonneg fun e _ ↦ by positivity
  -- the realisation equation, row by row
  have hrow : ∀ r, y (κ.slot r) = ∑ c, κ.matrix r c * z c := fun r ↦ by
    rw [← congrFun (κ.mulVec_coordsAt y) r]
    rfl
  let G := (Finset.univ : Finset (Fin (p + 1 + 1 + 1 + 3))).filter fun r ↦ IsGSlot (κ.slot r)
  set rk := κ.slot.symm (legSlot p k)
  -- each column of the leg row is dominated by four times the column sum over the G-rows
  have hcol : ∀ c, κ.matrix rk c * z c ≤ 4 * ∑ r ∈ G, κ.matrix r c * z c := by
    intro c
    have hRhs : 0 ≤ ∑ r ∈ G, κ.matrix r c * z c :=
      Finset.sum_nonneg fun r _ ↦ mul_nonneg (hM r c) (hz c)
    by_cases hE : (LeafFibre.rowFibre L rk (L.targetEdge c)).Nonempty
    · obtain ⟨e₀, he₀⟩ := hE
      obtain ⟨⟨hS₀, hR₀⟩, hT₀⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp he₀
      let n₀ : NonDanglingEdge κ.data := ⟨e₀, hS₀⟩
      have hRowOf : ∀ m : NonDanglingEdge κ.data, L.row m.stablePath = rk →
          κ.ident.row m.stablePath = legSlot p k := by
        intro m hR
        rw [ident_row_eq_slot, hR, Equiv.apply_symm_apply]
      have hRow₀ : κ.ident.row n₀.stablePath = legSlot p k := hRowOf n₀ hR₀
      -- by injectivity the leg has one edge over this column
      have hSingle : LeafFibre.rowFibre L rk (L.targetEdge c) = {e₀} := by
        ext e
        constructor
        · intro he
          obtain ⟨⟨hS, hR⟩, hT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp he
          have := hInj ⟨e, hS⟩ n₀ (hRowOf ⟨e, hS⟩ hR) hRow₀ (hT.trans hT₀.symm)
          exact Finset.mem_singleton.mpr (congrArg Subtype.val this)
        · intro he
          rw [Finset.mem_singleton] at he
          rw [he]
          exact he₀
      -- a G-edge over the same target edge
      have hNL := hNotLost n₀ hRow₀
      unfold IsLost at hNL
      push Not at hNL
      obtain ⟨eG, hG, hTG⟩ := hNL
      have hrG : L.row eG.stablePath ∈ G := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [← ident_row_eq_slot]
        exact hG
      have heG : eG.1 ∈ LeafFibre.rowFibre L (L.row eG.stablePath) (L.targetEdge c) :=
        (LeafFibre.mem_rowFibre _ _ _ _).mpr ⟨⟨eG.2, rfl⟩, hTG.trans hT₀⟩
      have hne : eG.1 ≠ e₀ := by
        intro h
        have hEq : eG = n₀ := Subtype.ext h
        rw [hEq, hRow₀] at hG
        exact legSlot_not_isGSlot k hG
      have hIdx := sourceEdgeIndex_add_le κ.data eG.1 e₀ hTG hne
      have hPos₀ := κ.data.sourceEdgeIndex_pos e₀
      have hPosG := κ.data.sourceEdgeIndex_pos eG.1
      have hLeG : (κ.data.sourceEdgeIndex eG.1 : ℚ) ≤ 4 := by
        exact_mod_cast (by omega : κ.data.sourceEdgeIndex eG.1 ≤ 4)
      have hPosG' : (0 : ℚ) < κ.data.sourceEdgeIndex eG.1 := by exact_mod_cast hPosG
      have hEk : κ.matrix rk c = 1 / κ.data.sourceEdgeIndex e₀ := by
        rw [hEntry, hSingle, Finset.sum_singleton]
      have hEG : 1 / (κ.data.sourceEdgeIndex eG.1 : ℚ) ≤ κ.matrix (L.row eG.stablePath) c := by
        rw [hEntry]
        exact Finset.single_le_sum (f := fun e ↦ (1 : ℚ) / κ.data.sourceEdgeIndex e)
          (fun e _ ↦ by positivity) heG
      have hOne : (1 : ℚ) / κ.data.sourceEdgeIndex e₀ ≤ 1 :=
        (div_le_one (by positivity)).mpr (Nat.one_le_cast.mpr hPos₀)
      have hFour : (1 : ℚ) ≤ 4 * (1 / κ.data.sourceEdgeIndex eG.1) := by
        rw [mul_one_div, le_div_iff₀ hPosG']
        linarith
      have hzc := hz c
      calc κ.matrix rk c * z c = 1 / κ.data.sourceEdgeIndex e₀ * z c := by rw [hEk]
        _ ≤ 1 * z c := mul_le_mul_of_nonneg_right hOne hzc
        _ ≤ (4 * (1 / κ.data.sourceEdgeIndex eG.1)) * z c :=
            mul_le_mul_of_nonneg_right hFour hzc
        _ = 4 * (1 / κ.data.sourceEdgeIndex eG.1 * z c) := by ring
        _ ≤ 4 * (κ.matrix (L.row eG.stablePath) c * z c) := by
            gcongr
        _ ≤ 4 * ∑ r ∈ G, κ.matrix r c * z c := by
            gcongr
            exact Finset.single_le_sum (f := fun r ↦ κ.matrix r c * z c)
              (fun r _ ↦ mul_nonneg (hM r c) hzc) hrG
    · rw [Finset.not_nonempty_iff_eq_empty] at hE
      rw [hEntry, hE, Finset.sum_empty, zero_mul]
      exact mul_nonneg (by norm_num) hRhs
  -- the G-rows add up to the total length of `G̃`
  have hG : ∑ i, baseRequest s y i = ∑ r ∈ G, y (κ.slot r) := by
    rw [sum_baseRequest]
    rw [Finset.sum_equiv κ.slot (t := (Finset.univ : Finset (Fin (p + 1 + 1 + 1 + 3))).filter
        fun j ↦ IsGSlot j) (g := y) (fun r ↦ by simp [G]) (fun r _ ↦ rfl)]
    conv_rhs => rw [Finset.sum_filter, Fin.sum_univ_add]
    have h1 : ∀ i : Fin (p + 1 + 1 + 1), IsGSlot (Fin.castAdd 3 i) := fun i ↦ by
      unfold IsGSlot
      simp only [Fin.val_castAdd]
      exact i.isLt
    have h2 : ∀ i : Fin 3, ¬ IsGSlot (Fin.natAdd (p + 1 + 1 + 1) i) := fun i ↦ by
      unfold IsGSlot
      simp only [Fin.val_natAdd]
      omega
    simp only [h1, h2, ↓reduceIte, Finset.sum_const_zero, add_zero]
    rfl
  have hleg : legLength y k = ∑ c, κ.matrix rk c * z c := by
    rw [← hrow rk]
    simp [rk, legLength]
  calc legLength y k = ∑ c, κ.matrix rk c * z c := hleg
    _ ≤ ∑ c, 4 * ∑ r ∈ G, κ.matrix r c * z c := Finset.sum_le_sum fun c _ ↦ hcol c
    _ = 4 * ∑ r ∈ G, ∑ c, κ.matrix r c * z c := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ = 4 * ∑ r ∈ G, y (κ.slot r) := by
        congr 1
        exact Finset.sum_congr rfl fun r _ ↦ (hrow r).symm
    _ = 4 * ∑ i, baseRequest s y i := by rw [hG]

/-- **At long legs every leg has a leaf detour when `φ(c) ∈ φ(G)`** (Theorem 4.7(a), first
bullet): otherwise Lemma 4.2(i) and Lemma 4.6 bound its length by `4 L(G)`. -/
theorem hasDetour_of_mem_gImage (hcubic : core.Cubic) (hconn : core.Connected)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    (hlong : LongLegs s y) (mem : FibreMember (tripodCore core s) y (3 + 2)) (hOpen : mem.Open)
    (hc : TripodFrame.centreTarget (Frame.of mem) ∈ TripodFrame.gImage (Frame.of mem))
    (k : Fin 3) : HasDetour (Frame.of mem) k := by
  by_contra hNo
  have hz : ∀ i, 0 ≤ (Frame.of mem).coordsAt y i := by
    rw [Frame.coordsAt_of]
    exact fun i ↦ (hOpen i).le
  have hLe := legLength_le_of_noDetour (Frame.of mem) hz k
    (legEdge_injective_of_noDetour (Frame.of mem) k hNo)
    (legEdge_not_isLost_of_noDetour hcubic hconn (Frame.of mem) k hNo hc)
  exact absurd (hlong k) (not_lt.mpr hLe)

-- The metric hypotheses (`hgenus`, `hpos`, `hlong`, `hOpen`) and cubicity are not used: the
-- count below needs only nonsingularity and Part I's local properties. They stay in the statement,
-- which consumers rely on.
set_option linter.unusedVariables false in
/-- **The parameter count: each detour is at its own mark** (Proposition 4.11, §4.8). If the
lost edges are exactly three leaf edges, the `k`-th carrying leg `k`, then every leg leaves its
mark up its leaf edge: the member is glued. The proof is in section 6 above: a mark lies over the
inner end `w_j` of every lost edge (Pairing and the column trick), the `w_j` are distinct, and at a
mark over `w_j` the leg leaves up `λ_j`. -/
theorem isGlued_of_lost_eq_detours (hcubic : core.Cubic) (hconn : core.Connected)
    (hgenus : p + 1 - n = 6)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (mem : FibreMember (tripodCore core s) y (3 + 2)) (hOpen : mem.Open)
    (hc : TripodFrame.centreTarget (Frame.of mem) ∈ TripodFrame.gImage (Frame.of mem))
    (e : Fin 3 → NonDanglingEdge mem.data)
    (hRow : ∀ k, mem.ident.row (e k).stablePath = legSlot p k)
    (hLeaf : ∀ k, IsLeafEdge mem.target (e k).1.1.1)
    (hLost : ∀ t, IsLost (Frame.of mem) t ↔ ∃ k, t = (e k).1.1.1) :
    MemberIsGlued mem := by
  classical
  set κ := Frame.of mem with hκ
  let lam : Fin 3 → κ.target.edges := fun k ↦ (e k).1.1.1
  have hLamLost : ∀ j, IsLost κ (lam j) := fun j ↦ (hLost _).mpr ⟨j, rfl⟩
  have hLeafLost : ∀ t, IsLost κ t → IsLeafEdge κ.target t := by
    intro t ht
    obtain ⟨j, rfl⟩ := (hLost t).mp ht
    exact hLeaf j
  have hInj : Function.Injective lam := fun i j h ↦
    leg_eq_of_isLeafEdge κ (e i) (e j) (hRow i) (hRow j) (hLeaf i) h.symm
  -- the inner end of each lost edge: trivalent, with two edges of `T̂`
  choose w a b hwt hTri ha hb using fun j ↦ exists_triEdges κ hc hLeafLost (hLamLost j)
  -- some mark lies over each inner end (Pairing and the column trick)
  have hMark : ∀ j, ∃ k, (TripodFrame.markSource κ k).1.1 = w j := by
    intro j
    by_contra hNo
    have hNo' : ∀ k, (TripodFrame.markSource κ k).1.1 ≠ w j := fun k h ↦ hNo ⟨k, h⟩
    exact false_of_matrix_eq κ lam hInj hLamLost (a := a j) (b := b j)
      (fun i h ↦ ha j (h ▸ hLamLost i)) (hTri j).hab
      (matrix_eq_of_trivalent_of_noMark κ (hTri j) (hLamLost j) hNo')
  choose kOf hkOf using hMark
  -- the inner ends are distinct, so every mark lies over one of them
  have hwInj : Function.Injective w := by
    intro i j hij
    have hmem : lam i ∈ GluingDatum.incidentEdges (w j) := by
      rw [← hij]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwt i⟩
    rcases ((hTri j).mem_iff _).mp hmem with h | h | h
    · exact hInj h
    · exact absurd (h ▸ hLamLost i) (ha j)
    · exact absurd (h ▸ hLamLost i) (hb j)
  have hkInj : Function.Injective kOf := by
    intro i j h
    apply hwInj
    rw [← hkOf i, ← hkOf j, h]
  have hkSurj : Function.Surjective kOf := Finite.injective_iff_surjective.mp hkInj
  -- so each leg leaves its mark up the lost leaf edge there
  show TripodFrame.IsGlued κ
  intro k
  obtain ⟨j, rfl⟩ := hkSurj k
  obtain ⟨ℓ, hℓX, hℓr⟩ := exists_legEdge_at_mark κ (kOf j)
  refine ⟨ℓ, hℓr, hℓX, ?_⟩
  rw [legEdge_target_of_mark_over κ (hTri j) (hLamLost j) (kOf j) (hkOf j) ℓ hℓX hℓr]
  exact hLeaf j

/-- **Not a claw ⇒ glued** (Theorem 4.7(a) with §4.8), for a connected `G̃`. -/
theorem isGlued_of_not_isClaw (hcubic : core.Cubic) (hconn : core.Connected)
    (hgenus : p + 1 - n = 6)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (mem : FibreMember (tripodCore core s) y (3 + 2)) (hOpen : mem.Open)
    (hNotClaw : ¬ MemberIsClaw mem) : MemberIsGlued mem := by
  have hc : TripodFrame.centreTarget (Frame.of mem) ∈ TripodFrame.gImage (Frame.of mem) := by
    by_contra h
    exact hNotClaw h
  choose e hRow hLeaf using hasDetour_of_mem_gImage hcubic hconn hlong mem hOpen hc
  exact isGlued_of_lost_eq_detours hcubic hconn hgenus hpos hlong mem hOpen hc e hRow hLeaf
    (isLost_iff_detour (Frame.of mem) e hRow hLeaf)

end Glued

/-! ## 8.  The dichotomy -/

/-- **Glued or claw, at long legs** (Theorem 4.7 and Corollary 4.10; §4.8). Over a
gadget whose base `G̃` is cubic of genus six, an open member of degree five at a request with long
legs is glued if and only if it is not a claw member. The same binders and conclusion as
`Classification.dichotomy`, which is this theorem. -/
theorem dichotomy {n p : ℕ} {core : Core n p} {s : MarkSlots p}
    (hcubic : core.Cubic) (hconn : core.Connected) (hgenus : p + 1 - n = 6)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (mem : FibreMember (tripodCore core s) y (3 + 2)) (hOpen : mem.Open) :
    MemberIsGlued mem ↔ ¬ MemberIsClaw mem := by
  refine ⟨fun hGlued hClaw ↦ not_isGlued_of_isClaw (Frame.of mem) hClaw hGlued, fun hNot ↦ ?_⟩
  exact isGlued_of_not_isClaw hcubic hconn hgenus hpos hlong mem hOpen hNot

end GenusSixExistence.Tripod.Dichotomy
