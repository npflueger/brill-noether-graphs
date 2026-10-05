module

public import GenusSixExistence.BrillNoetherRank.Tripod.Dichotomy
public import DraismaVargasCount.PassOnceLollipop
public import DraismaVargasCount.PendantRetraction
public import DraismaVargasCount.RowSlotOrientation
public import DraismaVargasCount.RowPosition
public import DraismaVargasCount.TreeMetricPotential

@[expose] public section

/-!
# The shape of a claw frame (Theorem 4.7(b), Lemma 4.8, Corollary 4.10)

Prose proof: `Research/genus-six-brill-noether-rank.md`, §4.3 (The shape of a leg), §4.6 (Claw
versus glued) and §4.7 (Leg indices, and the value of k₀); section and statement numbers in this
file refer to that note.

Throughout, `κ` is a frame of the gadget `Γ̃ = tripodCore core s` (any degree) whose centre lies
over a target vertex `c* = φ(c)` outside `T̂ = φ(G)` (`TripodFrame.IsClaw`), with `core`
connected. Nothing here uses long legs, closedness or the request.

## The facts, in the order they are proved

* `isLost_of_centre` — every target edge at `c*` is lost (no G-edge lies over it).
* `card_incidentEdges_centre` — `c*` is trivalent (Theorem 4.7(b)). A divalent `c*` would
  have a leaf edge (`exists_leaf_of_divalent`: cut at the edge `T̂` is not beyond; every edge beyond
  it is lost, so by the lost-edge bound a non-leaf edge there would end in a single leaf behind a
  divalent vertex, against `PassOnceLollipop.not_divalent_far_end`), and a leaf edge at a divalent
  `c*` is excluded by the indices at `c` (`false_of_divalent_of_leaf`, Part I `prop-local`
  r1-nd3).
* `isLost_iff` — the lost edges are exactly the three edges at `c*` (Theorem 4.7(b)).
* `lastEdge_target_injective`, `mem_centre_iff` — the last edges `ℓ_k` of the three legs (at
  `c`) lie over the three edges at `c*`, one each (Part I `prop-local` r0-nd3).
* `existsUnique_not_leaf` — exactly one of them lies over a non-leaf edge `f`; the other two
  edges at `c*` are leaf edges `t_v`, `t_{v′}` (Theorem 4.7(b); `not_two_far_ends`).
* `blockCard_centre`, `lastEdge_index` — `|c| = 1` and every `ℓ_k` has index one
  (Theorem 4.7(b)).
* `leafEdge_eq_of_legEdge` — a leg edge over a leaf edge lies over the target of the last edge of
  its own leg (Lemma 4.4 with the claw).
* `legEdge_eq_of_target_eq` — **pass-once on the legs**: two edges of one leg over one non-leaf
  target edge are equal (Lemma 4.2). A leg without a leaf detour is
  `legEdge_injective_of_noDetour`; on a detour leg the leaf excursion is the two edges of the row at
  the centre end, and the rest is a non-backtracking stretch (`nodup_targets_of_stretch`).
* `firstEdge_separates` — the target edge `h_k` under the first edge of leg `k` separates `c*`
  from `t_k = φ(k)` (Theorem 4.7(b), Corollary 4.3).
* `legEdge_index` — **leg indices**: every edge of every leg has index one (Lemma 4.8): an index
  change at a divalent `u` would make the two columns at `u` agree on the G-rows
  (`matrix_eq_of_divalent_of_row`), against the column trick `false_of_matrix_eq`.
* `sum_yCore_centre` — **`k₀ = 0`** in the form used by `RealisationProof`: the source vertices
  over `c*` that retract onto the tripod `Y` have total index three (Corollary 4.10). By the branch
  census `PendantRetraction.retractedFibre_eq_branch_sum` it is the tripod vertices over `c*`
  (the centre and two leg vertices, `sum_yCore_direct`) plus the dangling branches at the tripod
  through `c*`, of which there are none (`branch_avoids_centre`: pass-once, the handshake
  `markSource_iff_not_centreSource` at the two leg edges of a vertex, and the disjointness of the
  branches at a vertex, `not_beyond_both`).

The proof of `k₀ = 0` differs from Corollary 4.10, which evaluates the Riemann–Hurwitz identity
Proposition 4.9 on `Y′`: here the dangling trees are located directly, through the branch census
(§8.2).
-/

namespace GenusSixExistence.Tripod.ClawShape

open DraismaVargas.Count
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount incidenceCount_pos_iff)
open DraismaVargas.LocalCases.FullDimensionalSource (FullDimensionalSourcePresentation)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open GenusSixExistence.Tripod.Gadget
open GenusSixExistence.Tripod.Classification
open GenusSixExistence.Tripod.Dichotomy

variable {n p degree : ℕ} {core : Core n p} {s : MarkSlots p}
variable (κ : Frame (tripodCore core s) degree)

/-! ## 1.  The first and the last edge of a leg -/

/-- The leg `k` carries a surviving edge at the centre. -/
theorem exists_lastEdge (k : Fin 3) :
    ∃ ℓ : NonDanglingEdge κ.data, Incident κ.data ℓ.1 (centreSource κ) ∧
      κ.ident.row ℓ.stablePath = legSlot p k := by
  obtain ⟨ℓ, hℓ, hrow⟩ := exists_incident_of_end κ (legSlot p k) (centre n)
    (Or.inl (tripodCore_tail_legSlot k))
  exact ⟨ℓ, hℓ, by rw [hrow, Equiv.apply_symm_apply]⟩

/-- **The last edge `ℓ_k` of leg `k`**: its surviving edge at the centre. -/
noncomputable def lastEdge (k : Fin 3) : NonDanglingEdge κ.data :=
  (exists_lastEdge κ k).choose

theorem lastEdge_incident (k : Fin 3) : Incident κ.data (lastEdge κ k).1 (centreSource κ) :=
  (exists_lastEdge κ k).choose_spec.1

theorem lastEdge_row (k : Fin 3) : κ.ident.row (lastEdge κ k).stablePath = legSlot p k :=
  (exists_lastEdge κ k).choose_spec.2

/-- The centre carries exactly one surviving edge of each leg. -/
theorem lastEdge_unique (k : Fin 3) {g : NonDanglingEdge κ.data}
    (hg : Incident κ.data g.1 (centreSource κ)) (hr : κ.ident.row g.stablePath = legSlot p k) :
    g = lastEdge κ k := by
  classical
  have hInc := κ.ident.incidence (κ.ident.vertex.symm (centre n)) (legSlot p k)
  rw [Equiv.apply_symm_apply] at hInc
  have hOne : incidenceCount κ.data (centreSource κ) (κ.ident.row.symm (legSlot p k)) = 1 := by
    show incidenceCount κ.data (κ.ident.vertex.symm (centre n)).1 _ = 1
    rw [hInc]
    unfold coreIncidence
    rw [tripodCore_tail_legSlot, tripodCore_head_legSlot, ite_eq_left rfl,
      ite_eq_right (centre_ne_tripodMark k).symm]
  unfold incidenceCount at hOne
  refine Finset.card_le_one.mp hOne.le g ?_ (lastEdge κ k) ?_
  · exact Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr hg,
      (Equiv.eq_symm_apply _).mpr hr⟩
  · exact Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr
      (lastEdge_incident κ k), (Equiv.eq_symm_apply _).mpr (lastEdge_row κ k)⟩

/-- **The first edge `e_k` of leg `k`**: its surviving edge at the mark (the germ). -/
noncomputable def firstEdge (k : Fin 3) : NonDanglingEdge κ.data :=
  (exists_legEdge_at_mark κ k).choose

theorem firstEdge_incident (k : Fin 3) :
    Incident κ.data (firstEdge κ k).1 (TripodFrame.markSource κ k) :=
  (exists_legEdge_at_mark κ k).choose_spec.1

theorem firstEdge_row (k : Fin 3) : κ.ident.row (firstEdge κ k).stablePath = legSlot p k :=
  (exists_legEdge_at_mark κ k).choose_spec.2

theorem firstEdge_unique (k : Fin 3) {g : NonDanglingEdge κ.data}
    (hg : Incident κ.data g.1 (TripodFrame.markSource κ k))
    (hr : κ.ident.row g.stablePath = legSlot p k) : g = firstEdge κ k :=
  legEdge_unique_at_mark κ k hg (firstEdge_incident κ k) hr (firstEdge_row κ k)

/-! ## 2.  The edges at the centre -/

/-- **Every target edge at `φ(c)` is lost** in a claw frame: a G-edge over it would put `φ(c)`
in `φ(G)`. -/
theorem isLost_of_centre (hClaw : TripodFrame.IsClaw κ) {t : κ.target.edges}
    (ht : t ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ)) : IsLost κ t := by
  intro e hG he
  apply hClaw
  refine ⟨e, hG, ?_⟩
  rw [he]
  exact (Finset.mem_filter.mp ht).2

/-- The last edge of a leg lies over an edge at `φ(c)`. -/
theorem lastEdge_mem_centre (k : Fin 3) :
    (lastEdge κ k).1.1.1 ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ) :=
  ((incident_iff_target_mem_and_rel κ.data _ _).mp (lastEdge_incident κ k)).1

/-! ### Tree and branch facts used throughout -/

/-- The far end of a target edge at `w`. -/
theorem exists_far_end {T : CFGraph.{0}} {w : T.V} {t : T.edges}
    (ht : t ∈ GluingDatum.incidentEdges w) :
    ∃ x, ((t : T.V × T.V).1 = x ∨ (t : T.V × T.V).2 = x) ∧ x ≠ w ∧
      ∀ z, ((t : T.V × T.V).1 = z ∨ (t : T.V × T.V).2 = z) → z = w ∨ z = x := by
  have hne := TargetGeodesic.Dart.coe_fst_ne_snd t
  rcases (Finset.mem_filter.mp ht).2 with h | h
  · refine ⟨_, Or.inr rfl, fun e ↦ hne (h.trans e.symm), fun z hz ↦ ?_⟩
    rcases hz with hz | hz
    · exact Or.inl (hz.symm.trans h)
    · exact Or.inr hz.symm
  · refine ⟨_, Or.inl rfl, fun e ↦ hne (e.trans h.symm), fun z hz ↦ ?_⟩
    rcases hz with hz | hz
    · exact Or.inr hz.symm
    · exact Or.inl (hz.symm.trans h)

/-- A target predicate separates the ends of an edge exactly when it separates two distinct named
ends. -/
theorem iff_ends {V : Type*} {Q : V → Prop} {pr : V × V} {a b : V} (ha : pr.1 = a ∨ pr.2 = a)
    (hb : pr.1 = b ∨ pr.2 = b) (hab : a ≠ b) : (Q pr.1 ↔ Q pr.2) ↔ (Q a ↔ Q b) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.symm.trans hb) hab
  · rw [ha, hb]
  · rw [ha, hb]
    exact Iff.comm
  · exact absurd (ha.symm.trans hb) hab

/-- An edge with a leaf end is a leaf edge. -/
theorem isLeafEdge_of_end {T : CFGraph} {t : T.edges} {x : T.V}
    (hx : (t : T.V × T.V).1 = x ∨ (t : T.V × T.V).2 = x) (hl : IsLeafVertex T x) :
    IsLeafEdge T t := by
  have h := card_incidentEdges_eq_vertex_degree T x
  have h1 : vertex_degree T x = 1 := by
    rw [← h]
    unfold IsLeafVertex at hl
    rw [hl]
    rfl
  rcases hx with rfl | rfl
  · exact Or.inl h1
  · exact Or.inr h1

/-- The leaf edge at a leaf is a leaf edge. -/
theorem isLeafEdge_leafEdge {T : CFGraph} {v : T.V} (hv : IsLeafVertex T v) :
    IsLeafEdge T (leafEdge hv) :=
  isLeafEdge_of_end (Finset.mem_filter.mp (leafEdge_mem hv)).2 hv

section TreeSides

variable {G : CFGraph.{0}} (A : TargetGeodesic.TreeRank G)

/-- **The branches beyond two distinct edges at a vertex are disjoint**: no vertex `x` is across
the cut at `g` from `u` and across the cut at `g'` from `u`, for distinct edges `g, g'` at `u`. -/
theorem not_beyond_both {u x : G.V} {g g' : G.edges}
    (hg : (g : G.V × G.V).1 = u ∨ (g : G.V × G.V).2 = u)
    (hg' : (g' : G.V × G.V).1 = u ∨ (g' : G.V × G.V).2 = u) (hne : g ≠ g')
    (h1 : ¬ (Below A g x ↔ Below A g u)) (h2 : ¬ (Below A g' x ↔ Below A g' u)) : False := by
  have hlo : ∀ {e : G.edges}, u = A.low e → ¬ Below A e u := fun h ↦ h ▸ not_below_low_self A _
  have hhi : ∀ {e : G.edges}, u = A.high e → Below A e u := fun h ↦ h ▸ below_high_self A _
  have hBelow : ∀ {e : G.edges}, u = A.low e → ¬ (Below A e x ↔ Below A e u) → Below A e x :=
    fun he h ↦ by
      by_contra hx
      exact h ⟨fun h' ↦ absurd h' hx, fun h' ↦ absurd h' (hlo he)⟩
  have hNotBelow : ∀ {e : G.edges}, u = A.high e → ¬ (Below A e x ↔ Below A e u) →
      ¬ Below A e x := fun he h hx ↦ h ⟨fun _ ↦ hhi he, fun _ ↦ hx⟩
  -- below an edge with lower end `u`, hence below `u`'s own upper edge
  have hUp : ∀ {e e' : G.edges}, u = A.low e → u = A.high e' → Below A e x → Below A e' x := by
    rintro e e' he he' ⟨j, hj⟩
    refine ⟨j + 1, ?_⟩
    rw [Function.iterate_succ_apply', hj, A.up_high, ← he, he']
  -- two subtrees hanging from `u` are disjoint
  have hTwoLow : ∀ {e e' : G.edges}, u = A.low e → u = A.low e' → ∀ i d : ℕ,
      A.up^[i] x = A.high e → A.up^[d + 1 + i] x = A.high e' → False := by
    intro e e' he he' i d hi hj
    rw [Function.iterate_add_apply, hi, Function.iterate_succ_apply, A.up_high, ← he] at hj
    have h1 := A.rank_iterate_up_le d u
    rw [hj] at h1
    have h2 := A.rank_low_lt e'
    rw [← he'] at h2
    omega
  rcases A.eq_low_or_eq_high hg with hgl | hgh <;>
    rcases A.eq_low_or_eq_high hg' with hgl' | hgh'
  · obtain ⟨i, hi⟩ := hBelow hgl h1
    obtain ⟨j, hj⟩ := hBelow hgl' h2
    rcases Nat.lt_trichotomy i j with hij | rfl | hij
    · obtain ⟨d, rfl⟩ : ∃ d, j = d + 1 + i := ⟨j - i - 1, by omega⟩
      exact hTwoLow hgl hgl' i d hi hj
    · exact hne (A.high_injective (hi.symm.trans hj))
    · obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 + j := ⟨i - j - 1, by omega⟩
      exact hTwoLow hgl' hgl j d hj hi
  · exact hNotBelow hgh' h2 (hUp hgl hgh' (hBelow hgl h1))
  · exact hNotBelow hgh h1 (hUp hgl' hgh (hBelow hgl' h2))
  · exact hne (A.high_injective (hgh.symm.trans hgh'))

/-- **A walk avoiding `u` does not cross an edge at `u`.** -/
theorem below_iff_of_reachP {t : G.edges} {u : G.V}
    (htu : (t : G.V × G.V).1 = u ∨ (t : G.V × G.V).2 = u) {y z : G.V} (hy : y ≠ u)
    (h : DanglingSideStructure.ReachP G (fun x ↦ x ≠ u) y z) : Below A t y ↔ Below A t z := by
  have key : (Below A t y ↔ Below A t z) ∧ z ≠ u := by
    induction h with
    | refl => exact ⟨Iff.rfl, hy⟩
    | @tail b c _ hstep ih =>
      obtain ⟨hbc, hc⟩ := hstep
      refine ⟨ih.1.trans ?_, hc⟩
      unfold num_edges at hbc
      obtain ⟨e, he⟩ := Multiset.card_pos_iff_exists_mem.mp hbc
      obtain ⟨heT, hev⟩ := Multiset.mem_filter.mp he
      let t' : G.edges := ⟨e, ⟨0, Multiset.count_pos.mpr heT⟩⟩
      have hne : t' ≠ t := by
        intro hEq
        have hu : (t' : G.V × G.V).1 = u ∨ (t' : G.V × G.V).2 = u := hEq ▸ htu
        change e.1 = u ∨ e.2 = u at hu
        rcases hev with rfl | rfl <;> rcases hu with hu | hu
        · exact ih.2 hu
        · exact hc hu
        · exact hc hu
        · exact ih.2 hu
      have hiff := (below_fst_iff_snd A t t').mpr hne
      change Below A t e.1 ↔ Below A t e.2 at hiff
      rcases hev with rfl | rfl
      · exact hiff
      · exact hiff.symm
  exact key.1

end TreeSides

/-- **A branch vertex over `φ(c)` is the centre**: any other branch vertex is a mark or a vertex of
`G`, and lies over `T̂`. -/
theorem eq_centre_of_branch (hClaw : TripodFrame.IsClaw κ) {β : κ.data.SourceVertex}
    (hβ : 3 ≤ nonDanglingValency κ.data β) (hc : β.1.1 = TripodFrame.centreTarget κ) :
    β = centreSource κ := by
  by_contra hne
  obtain ⟨g, hg⟩ := exists_nonDanglingEdge_incident β (by omega)
  have hb : κ.ident.vertex.symm (κ.ident.vertex ⟨β, hβ⟩) = ⟨β, hβ⟩ :=
    Equiv.symm_apply_apply _ _
  have hg' : Incident κ.data g.1 (κ.ident.vertex.symm (κ.ident.vertex ⟨β, hβ⟩)).1 :=
    (congrArg (fun b : StableGraphIncidence.BranchVertex κ.data ↦ Incident κ.data g.1 b.1) hb).mpr
      hg
  have hEnd := end_of_incident_vertex κ (κ.ident.vertex ⟨β, hβ⟩) g hg'
  rcases isGSlot_or_eq_legSlot (κ.ident.row g.stablePath) with hG | ⟨m, hm⟩
  · exact hClaw (hc ▸ ⟨g, hG, incident_target hg⟩)
  · rw [hm, tripodCore_tail_legSlot, tripodCore_head_legSlot] at hEnd
    rcases hEnd with h | h
    · exact hne (congrArg Subtype.val ((Equiv.symm_apply_eq κ.ident.vertex).mpr h)).symm
    · have hβm : β = TripodFrame.markSource κ m :=
        (congrArg Subtype.val ((Equiv.symm_apply_eq κ.ident.vertex).mpr h)).symm
      exact hClaw (hc ▸ hβm ▸ markTarget_mem_gImage κ m)

/-! ## 3.  The last edges, the leaf edges at `φ(c)`, and the indices at the centre -/

theorem fin3_exists_third : ∀ a b : Fin 3, a ≠ b → ∃ m : Fin 3, m ≠ a ∧ m ≠ b := by decide

theorem fin3_cases : ∀ a b c m : Fin 3, a ≠ b → c ≠ a → c ≠ b → m = a ∨ m = b ∨ m = c := by
  decide

/-- The last edges of distinct legs are distinct. -/
theorem lastEdge_ne {k k' : Fin 3} (h : k ≠ k') : (lastEdge κ k).1 ≠ (lastEdge κ k').1 := by
  intro hEq
  have hE : lastEdge κ k = lastEdge κ k' := Subtype.ext hEq
  have hr := lastEdge_row κ k
  rw [hE, lastEdge_row] at hr
  exact h (legSlot_injective hr.symm)

/-- Every surviving edge at the centre is the last edge of a leg. -/
theorem exists_eq_lastEdge {g : κ.data.SourceEdge}
    (hg : g ∈ nonDanglingIncident κ.data (centreSource κ)) : ∃ m, g = (lastEdge κ m).1 := by
  obtain ⟨gS, gI⟩ := (mem_nonDanglingIncident _ _ _).mp hg
  rcases isGSlot_or_eq_legSlot (κ.ident.row (NonDanglingEdge.stablePath ⟨g, gS⟩)) with
    hG | ⟨m, hm⟩
  · exact absurd hG (not_isGSlot_of_incident_centre κ ⟨g, gS⟩ gI)
  · exact ⟨m, congrArg Subtype.val (lastEdge_unique κ m gI hm)⟩

theorem lastEdge_mem_nonDanglingIncident (k : Fin 3) :
    (lastEdge κ k).1 ∈ nonDanglingIncident κ.data (centreSource κ) :=
  (mem_nonDanglingIncident _ _ _).mpr ⟨(lastEdge κ k).2, lastEdge_incident κ k⟩

/-- **The surviving edges at the centre are the three last edges.** -/
theorem nonDanglingIncident_centre :
    nonDanglingIncident κ.data (centreSource κ) =
      Finset.univ.image fun k ↦ (lastEdge κ k).1 := by
  ext g
  constructor
  · intro hg
    obtain ⟨m, rfl⟩ := exists_eq_lastEdge κ hg
    exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩
  · intro hg
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hg
    exact lastEdge_mem_nonDanglingIncident κ m

theorem lastEdge_val_injective : Function.Injective fun k ↦ (lastEdge κ k).1 := by
  intro k k' h
  by_contra hne
  exact lastEdge_ne κ hne h

/-- The centre has surviving valency three. -/
theorem nonDanglingValency_centre : nonDanglingValency κ.data (centreSource κ) = 3 :=
  le_antisymm (κ.fullDim.trivalent _) (three_le_centreSource κ)

/-! ### Excluding a divalent `φ(c)` -/

/-- A branch vertex other than the centre lies over `T̂`: it is a mark or a vertex of `G`. -/
theorem branch_mem_gImage {β : κ.data.SourceVertex} (hβ : 3 ≤ nonDanglingValency κ.data β)
    (hne : β ≠ centreSource κ) : β.1.1 ∈ TripodFrame.gImage κ := by
  obtain ⟨g, hg⟩ := exists_nonDanglingEdge_incident β (by omega)
  have hb : κ.ident.vertex.symm (κ.ident.vertex ⟨β, hβ⟩) = ⟨β, hβ⟩ :=
    Equiv.symm_apply_apply _ _
  have hg' : Incident κ.data g.1 (κ.ident.vertex.symm (κ.ident.vertex ⟨β, hβ⟩)).1 :=
    (congrArg (fun b : StableGraphIncidence.BranchVertex κ.data ↦ Incident κ.data g.1 b.1) hb).mpr
      hg
  have hEnd := end_of_incident_vertex κ (κ.ident.vertex ⟨β, hβ⟩) g hg'
  rcases isGSlot_or_eq_legSlot (κ.ident.row g.stablePath) with hG | ⟨m, hm⟩
  · exact ⟨g, hG, incident_target hg⟩
  · rw [hm, tripodCore_tail_legSlot, tripodCore_head_legSlot] at hEnd
    rcases hEnd with h | h
    · exact absurd (congrArg Subtype.val ((Equiv.symm_apply_eq κ.ident.vertex).mpr h)).symm hne
    · have hβm : β = TripodFrame.markSource κ m :=
        (congrArg Subtype.val ((Equiv.symm_apply_eq κ.ident.vertex).mpr h)).symm
      rw [hβm]
      exact markTarget_mem_gImage κ m

/-- **A divalent `φ(c)` has no leaf edge** (Theorem 4.7(b); Part I `prop-local`, the case
r1-nd3). Its two
edges are the targets of the three last edges (`not_forall_target_eq`, with `r(c) ≤ 1`). Two last
edges over one leaf edge would lie on one stable path (Lemma 4.4), so a leaf edge `b` carries exactly
one, `ℓ_r`, of index one, and the other two lie over the other edge `a`, with indices adding up to at
most `|c|`. The index form `|ℓ₀| + |ℓ₁| + |ℓ₂| = 2|c| + 1 - r(c)` then forces `|c| = 1` and
`|ℓ_p| + |ℓ_q| = 1`, which is impossible. -/
theorem false_of_divalent_of_leaf
    (h2 : (GluingDatum.incidentEdges (TripodFrame.centreTarget κ)).card = 2)
    {b : κ.target.edges} (hb : b ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ))
    (hbl : IsLeafEdge κ.target b) : False := by
  classical
  obtain ⟨v, hv, hvb⟩ := exists_leaf_of_isLeafEdge hbl
  have h3c := nonDanglingValency_centre κ
  have hr1 : κ.data.localRamification (centreSource κ).1.1
      ⟨(centreSource κ).1.2, (centreSource κ).2⟩ ≤ 1 :=
    DivalentSourceLocal.localRamification_le_one_of_nonleaf κ.data κ.fullDim.valid
      (centreSource κ) (κ.fullDim.changeMinimal _) (by
        change 2 ≤ (GluingDatum.incidentEdges (TripodFrame.centreTarget κ)).card
        rw [h2])
  have hr0 := κ.data.localRamification_nonneg _ (κ.fullDim.valid.2 _)
    ⟨(centreSource κ).1.2, (centreSource κ).2⟩
  obtain ⟨a, haM, hab⟩ := Finset.exists_mem_ne (show 1 < (GluingDatum.incidentEdges
    (TripodFrame.centreTarget κ)).card by omega) b
  have hInc : ∀ t ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ), t = a ∨ t = b := by
    intro t ht
    by_contra hNo
    push Not at hNo
    have hsub : ({t, a, b} : Finset κ.target.edges) ⊆
        GluingDatum.incidentEdges (TripodFrame.centreTarget κ) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ht
      · exact haM
      · exact hb
    have hle := Finset.card_le_card hsub
    rw [h2, Finset.card_insert_of_notMem (by simp [hNo.1, hNo.2]), Finset.card_pair hab] at hle
    omega
  obtain ⟨r, hr⟩ : ∃ r, (lastEdge κ r).1.1.1 = b := by
    by_contra hNo
    push Not at hNo
    apply not_forall_target_eq κ.fullDim.danglingEdgeNoGlue h3c hr1 a
    intro g hg
    obtain ⟨m, rfl⟩ := exists_eq_lastEdge κ hg
    rcases hInc _ (lastEdge_mem_centre κ m) with h | h
    · exact h
    · exact absurd h (hNo m)
  have hOther : ∀ m, m ≠ r → (lastEdge κ m).1.1.1 = a := by
    intro m hm
    rcases hInc _ (lastEdge_mem_centre κ m) with h | h
    · exact h
    · exact absurd (leg_eq_of_isLeafEdge κ (lastEdge κ m) (lastEdge κ r) (lastEdge_row κ m)
        (lastEdge_row κ r) (h ▸ hbl) (hr.trans h.symm)) hm
  have hSum := sum_index_nonDanglingIncident κ.fullDim.danglingEdgeNoGlue (centreSource κ)
  rw [nonDanglingIncident_centre,
    Finset.sum_image (fun a _ b _ h ↦ lastEdge_val_injective κ h), h3c, Fin.sum_univ_three] at hSum
  have hR : ∀ m, m = r → κ.data.sourceEdgeIndex (lastEdge κ m).1 = 1 := fun m hm ↦ by
    subst hm
    exact LeafFibre.sourceEdgeIndex_eq_one_above_leaf κ.fullDim hv (hr.trans hvb)
  have hPair : ∀ p q, p ≠ q → p ≠ r → q ≠ r →
      κ.data.sourceEdgeIndex (lastEdge κ p).1 + κ.data.sourceEdgeIndex (lastEdge κ q).1 ≤
        (κ.data.vertexPartition (centreSource κ).1.1).blockCard (centreSource κ).1.2 :=
    fun p q hpq hp hq ↦ RowWalk.sourceEdgeIndex_add_le_blockCard κ.data (lastEdge_incident κ p)
      (lastEdge_incident κ q) (lastEdge_ne κ hpq) ((hOther p hp).trans (hOther q hq).symm)
  have hP0 := GluingDatum.sourceEdgeIndex_pos κ.data (lastEdge κ 0).1
  have hP1 := GluingDatum.sourceEdgeIndex_pos κ.data (lastEdge κ 1).1
  have hP2 := GluingDatum.sourceEdgeIndex_pos κ.data (lastEdge κ 2).1
  push_cast at hSum
  fin_cases r
  · have := hR 0 rfl
    have := hPair 1 2 (by decide) (by decide) (by decide)
    omega
  · have := hR 1 rfl
    have := hPair 0 2 (by decide) (by decide) (by decide)
    omega
  · have := hR 2 rfl
    have := hPair 0 1 (by decide) (by decide) (by decide)
    omega

/-- **A divalent `φ(c)` has a leaf edge** (Theorem 4.7(b)). Cut at the edge `b` at
`φ(c)` beyond which the mark image `φ(0)` does not lie (two such edges cannot both separate it from
`φ(c)`, `not_beyond_both`). All of `T̂` is on `φ(c)`'s side of `b` (`b` is lost,
`iff_of_mem_gImage`), so every edge with an end beyond `b` is lost. If `b` were not a leaf edge, its
far end `x_b` would have a second edge `g`, lost, and with the two edges at `φ(c)` these are all the
lost edges (`card_le_three_of_isLost`): `x_b` is divalent and the far end `z` of `g` is a leaf. The
leaf fold over `z` then has two distinct neighbours of surviving valency two over the divalent
`x_b` (no branch vertex lies over `x_b ∉ T̂`, and a fold whose two edges meet one vertex would make
a stable path with no end), which `PassOnceLollipop.not_divalent_far_end` forbids. -/
theorem exists_leaf_of_divalent (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    (h2 : (GluingDatum.incidentEdges (TripodFrame.centreTarget κ)).card = 2) :
    ∃ b ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ), IsLeafEdge κ.target b := by
  classical
  obtain ⟨A⟩ := TargetGeodesic.exists_treeRank κ.target κ.fullDim.targetConnected
    κ.fullDim.targetGenus
  set cs := TripodFrame.centreTarget κ with hcs
  obtain ⟨e1, e2, h12, hInc12⟩ := Finset.card_eq_two.mp h2
  have he1 : e1 ∈ GluingDatum.incidentEdges cs := by rw [hInc12]; simp
  have he2 : e2 ∈ GluingDatum.incidentEdges cs := by rw [hInc12]; simp
  have hyG := markTarget_mem_gImage κ 0
  -- the cut `b`
  obtain ⟨b, hbM, hbT⟩ : ∃ b ∈ GluingDatum.incidentEdges cs,
      (Below A b (TripodFrame.markSource κ 0).1.1 ↔ Below A b cs) := by
    by_contra hNo
    exact not_beyond_both A (Finset.mem_filter.mp he1).2 (Finset.mem_filter.mp he2).2 h12
      (fun h ↦ hNo ⟨e1, he1, h⟩) (fun h ↦ hNo ⟨e2, he2, h⟩)
  refine ⟨b, hbM, ?_⟩
  have hbc := (Finset.mem_filter.mp hbM).2
  have hbLost := isLost_of_centre κ hClaw hbM
  have hSideT : ∀ x ∈ TripodFrame.gImage κ, (Below A b x ↔ Below A b cs) := fun x hx ↦
    (iff_of_mem_gImage hconn κ (fun a ha ↦ (below_fst_iff_snd A _ _).mpr (hbLost a ha)) hx
      hyG).trans hbT
  have hBeyondLost : ∀ (g : κ.target.edges) (x : κ.target.V),
      ((g : κ.target.V × κ.target.V).1 = x ∨ (g : κ.target.V × κ.target.V).2 = x) →
      ¬ (Below A b x ↔ Below A b cs) → IsLost κ g := by
    intro g x hgx hx e he heg
    exact hx (hSideT x ⟨e, he, by rw [heg]; exact hgx⟩)
  have hNotThrough : ∀ {t : κ.target.edges} {p q : κ.target.V},
      ((t : κ.target.V × κ.target.V).1 = p ∨ (t : κ.target.V × κ.target.V).2 = p) →
      ((t : κ.target.V × κ.target.V).1 = q ∨ (t : κ.target.V × κ.target.V).2 = q) → p ≠ q →
      t ≠ b → (Below A b p ↔ Below A b q) := fun hp hq hpq htb ↦
    (iff_ends hp hq hpq).mp ((below_fst_iff_snd A b _).mpr htb)
  obtain ⟨xb, hxb, hxbc, hxbE⟩ := exists_far_end hbM
  have hxbB : ¬ (Below A b xb ↔ Below A b cs) := by
    intro h
    exact (below_fst_iff_snd A b b).mp ((iff_ends hxb hbc hxbc).mpr h) rfl
  by_contra hbL
  have hxbl : ¬ IsLeafVertex κ.target xb := fun h ↦ hbL (isLeafEdge_of_end hxb h)
  have hxbG : xb ∉ TripodFrame.gImage κ := fun h ↦ hxbB (hSideT xb h)
  -- the other edge `a`, whose far end is on `φ(c)`'s side of `b`
  obtain ⟨a, haM, hab⟩ := Finset.exists_mem_ne (show 1 < (GluingDatum.incidentEdges cs).card by
    omega) b
  have hac := (Finset.mem_filter.mp haM).2
  have haLost := isLost_of_centre κ hClaw haM
  obtain ⟨xa, hxa, hxac, hxaE⟩ := exists_far_end haM
  have hxaN : Below A b xa ↔ Below A b cs := hNotThrough hxa hac hxac hab
  have hNotA : ∀ x : κ.target.V,
      ((a : κ.target.V × κ.target.V).1 = x ∨ (a : κ.target.V × κ.target.V).2 = x) →
      ¬ ¬ (Below A b x ↔ Below A b cs) := by
    intro x hx hxB
    rcases hxaE x hx with h | h
    · exact hxB (by rw [h])
    · exact hxB (by rw [h]; exact hxaN)
  -- a second edge `g` at `x_b`, lost
  have hxbM : b ∈ GluingDatum.incidentEdges xb := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxb⟩
  have hxbCard : 1 < (GluingDatum.incidentEdges xb).card := by
    have h1 : (GluingDatum.incidentEdges xb).card ≠ 1 := hxbl
    have h0 : 0 < (GluingDatum.incidentEdges xb).card := Finset.card_pos.mpr ⟨b, hxbM⟩
    omega
  obtain ⟨g, hgM, hgb⟩ := Finset.exists_mem_ne hxbCard b
  have hgx := (Finset.mem_filter.mp hgM).2
  have hgLost := hBeyondLost g xb hgx hxbB
  have hga : g ≠ a := by
    rintro rfl
    exact hNotA xb hgx hxbB
  obtain ⟨z, hz, hzx, -⟩ := exists_far_end hgM
  have hzB : ¬ (Below A b z ↔ Below A b cs) := fun h ↦
    hxbB ((hNotThrough hgx hz (Ne.symm hzx) hgb).trans h)
  -- `a`, `b`, `g` are all the lost edges
  have hFour : ∀ t, IsLost κ t → t = a ∨ t = b ∨ t = g := by
    intro t ht
    by_contra hNo
    push Not at hNo
    have hAll : ∀ u ∈ ({t, a, b, g} : Finset κ.target.edges), IsLost κ u := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact ht
      · exact haLost
      · exact hbLost
      · exact hgLost
    have hCard := card_le_three_of_isLost κ _ hAll
    rw [Finset.card_insert_of_notMem (by simp [hNo.1, hNo.2.1, hNo.2.2]),
      Finset.card_insert_of_notMem (by simp [hab, Ne.symm hga]),
      Finset.card_pair (Ne.symm hgb)] at hCard
    omega
  -- `z` is a leaf
  have hzl : IsLeafVertex κ.target z := by
    by_contra hzl
    have hgz : g ∈ GluingDatum.incidentEdges z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    have hzCard : 1 < (GluingDatum.incidentEdges z).card := by
      have h1 : (GluingDatum.incidentEdges z).card ≠ 1 := hzl
      have h0 : 0 < (GluingDatum.incidentEdges z).card := Finset.card_pos.mpr ⟨g, hgz⟩
      omega
    obtain ⟨g3, hg3M, hg3g⟩ := Finset.exists_mem_ne hzCard g
    have hg3z := (Finset.mem_filter.mp hg3M).2
    rcases hFour g3 (hBeyondLost g3 z hg3z hzB) with h | h | h
    · subst h
      exact hNotA z hg3z hzB
    · subst h
      rcases hxbE z hg3z with h' | h'
      · exact hzB (by rw [h'])
      · exact hzx h'
    · exact hg3g h
  -- `x_b` is divalent
  have hxbDiv : (GluingDatum.incidentEdges xb).card = 2 := by
    by_contra hne
    obtain ⟨g2, hg2M, hg2b, hg2g⟩ : ∃ g2 ∈ GluingDatum.incidentEdges xb, g2 ≠ b ∧ g2 ≠ g := by
      by_contra hNo
      push Not at hNo
      have hsub : GluingDatum.incidentEdges xb ⊆ {b, g} := by
        intro x hx
        by_cases hxb' : x = b
        · simp [hxb']
        · simp [hNo x hx hxb']
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair (Ne.symm hgb)] at hle
      omega
    have hg2x := (Finset.mem_filter.mp hg2M).2
    rcases hFour g2 (hBeyondLost g2 xb hg2x hxbB) with h | h | h
    · subst h
      exact hNotA xb hg2x hxbB
    · exact hg2b h
    · exact hg2g h
  -- the leaf fold over `z` and its two neighbours over `x_b`
  have hgz : g ∈ GluingDatum.incidentEdges z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  have hgLeaf : g = leafEdge hzl := eq_leafEdge_of_mem hzl hgz
  obtain ⟨f1, f2, hf12, hSurv⟩ :=
    Finset.card_eq_two.mp (LeafFibre.leafSurvivors_card κ.fullDim hzl)
  have hf1 : f1 ∈ LeafFibre.leafSurvivors hzl := by rw [hSurv]; simp
  have hf2 : f2 ∈ LeafFibre.leafSurvivors hzl := by rw [hSurv]; simp
  obtain ⟨hf1S, hf1t⟩ := (LeafFibre.mem_leafSurvivors hzl).mp hf1
  obtain ⟨hf2S, hf2t⟩ := (LeafFibre.mem_leafSurvivors hzl).mp hf2
  have hf1x : f1.1.1 ∈ GluingDatum.incidentEdges xb := by rw [hf1t, ← hgLeaf]; exact hgM
  have hf2x : f2.1.1 ∈ GluingDatum.incidentEdges xb := by rw [hf2t, ← hgLeaf]; exact hgM
  set X1 := endOver κ.data f1 xb with hX1
  set X2 := endOver κ.data f2 xb with hX2
  have hX1I : Incident κ.data f1 X1 := endOver_incident κ.data f1 xb
  have hX2I : Incident κ.data f2 X2 := endOver_incident κ.data f2 xb
  have hX1t : X1.1.1 = xb := endOver_target κ.data hf1x
  have hX2t : X2.1.1 = xb := endOver_target κ.data hf2x
  have hA1 := LeafFibre.incident_coreVertex_of_mem_leafSurvivors κ.fullDim hzl hf1
  have hA2 := LeafFibre.incident_coreVertex_of_mem_leafSurvivors κ.fullDim hzl hf2
  have hXA : ∀ X : κ.data.SourceVertex, X.1.1 = xb → X ≠ LeafFibre.coreVertex κ.fullDim hzl :=
    fun X hX h ↦ hzx ((congrArg (fun v : κ.data.SourceVertex ↦ v.1.1) h).symm.trans hX)
  have hXv : ∀ {f : κ.data.SourceEdge} {X : κ.data.SourceVertex}, ¬ IsDangling κ.data f →
      Incident κ.data f X → X.1.1 = xb → nonDanglingValency κ.data X = 2 := by
    intro f X hfS hfX hXt
    have hpos : 0 < nonDanglingValency κ.data X := by
      rw [← card_nonDanglingIncident]
      exact Finset.card_pos.mpr ⟨f, (mem_nonDanglingIncident _ _ _).mpr ⟨hfS, hfX⟩⟩
    rcases κ.fullDim.nonDanglingValency_trichotomy X with h | h | h
    · omega
    · exact h
    · exfalso
      by_cases hXc : X = centreSource κ
      · exact hxbc (hXt.symm.trans (congrArg (fun v : κ.data.SourceVertex ↦ v.1.1) hXc))
      · exact hxbG (hXt ▸ branch_mem_gImage κ h.ge hXc)
  have hv1 := hXv hf1S hX1I hX1t
  have hv2 := hXv hf2S hX2I hX2t
  have hX12 : X1 ≠ X2 := by
    intro hEq
    have hAv := LeafFibre.nonDanglingValency_coreVertex κ.fullDim hzl
    have hX1f2 : Incident κ.data f2 X1 := hEq ▸ hX2I
    have hXA1 := hXA X1 hX1t
    -- the ends of `f1`, `f2` are the fold and `X1`
    have hEnds : ∀ {f : κ.data.SourceEdge}, (f = f1 ∨ f = f2) → ∀ V, Incident κ.data f V →
        V = LeafFibre.coreVertex κ.fullDim hzl ∨ V = X1 := by
      intro f hf V hV
      have hfA : Incident κ.data f (LeafFibre.coreVertex κ.fullDim hzl) := by
        rcases hf with rfl | rfl
        · exact hA1
        · exact hA2
      have hfX : Incident κ.data f X1 := by
        rcases hf with rfl | rfl
        · exact hX1I
        · exact hX1f2
      rcases eq_or_eq_otherEnd κ.data hfA hV with h | h
      · exact Or.inl h
      · right
        rcases eq_or_eq_otherEnd κ.data hfA hfX with h' | h'
        · exact absurd h' hXA1
        · exact h.trans h'.symm
    -- the surviving edges at the fold and at `X1` are `f1`, `f2`
    have hAt : ∀ V, (V = LeafFibre.coreVertex κ.fullDim hzl ∨ V = X1) →
        ∀ f' : κ.data.SourceEdge, ¬ IsDangling κ.data f' → Incident κ.data f' V →
          f' = f1 ∨ f' = f2 := by
      intro V hV f' hf'S hf'V
      rcases hV with rfl | rfl
      · have hm := LeafFibre.mem_leafSurvivors_of_incident_coreVertex κ.fullDim hzl hf'S hf'V
        rw [hSurv] at hm
        simpa using hm
      · exact IndexPattern.eq_or_eq_of_nonDanglingValency_two hv1 hf1S hX1I hf2S hX1f2 hf12
          hf'S hf'V
    -- so the stable path of `f1` has no end
    obtain ⟨first, vertex, hfirst, hEnd⟩ := κ.fullDim.pathEnds ⟨f1, hf1S⟩
    have hClosed : ∀ x y : NonDanglingEdge κ.data, Consecutive κ.data x y →
        (x.1 = f1 ∨ x.1 = f2) → (y.1 = f1 ∨ y.1 = f2) := by
      rintro x y ⟨-, V, hxV, hyV, -⟩ hx
      exact hAt V (hEnds hx V hxV) y.1 y.2 hyV
    have hP := (eqvGen_iff_of_closed hClosed ((stablePath_eq_iff _ _).mp hfirst)).mpr
      (Or.inl rfl)
    obtain ⟨hInc, hval⟩ := hEnd
    rcases hEnds hP vertex hInc with h | h
    · rw [h] at hval
      exact hval hAv
    · rw [h] at hval
      exact hval hv1
  have hOn2 : NonDanglingEdge.stablePath (⟨f2, hf2S⟩ : NonDanglingEdge κ.data) =
      NonDanglingEdge.stablePath (⟨f1, hf1S⟩ : NonDanglingEdge κ.data) :=
    (LeafFibre.stablePath_eq_of_mem_leafSurvivors κ.fullDim hzl hf2 hf2S).trans
      (LeafFibre.stablePath_eq_of_mem_leafSurvivors κ.fullDim hzl hf1 hf1S).symm
  exact PassOnceLollipop.not_divalent_far_end κ.fullDim
    (path := NonDanglingEdge.stablePath ⟨f1, hf1S⟩) hzl
    (LeafFibre.row_eq_leafRow κ.fullDim hzl hf1 hf1S).symm hX12 (hX1t.trans hX2t.symm)
    hv1 hv2 (hXA X1 hX1t) (hXA X2 hX2t) ⟨hf1S, rfl⟩ ⟨hf2S, hOn2⟩ hf1t hf2t hX1I hX2I
    (by rw [hX1t]; exact hxbDiv)

/-- **`φ(c)` is trivalent** (Theorem 4.7(b)). It is not a leaf (the centre has surviving
valency three), it has valency at most three (change-minimality), and a divalent `φ(c)` would have a
leaf edge (`exists_leaf_of_divalent`), which `false_of_divalent_of_leaf` excludes. -/
theorem card_incidentEdges_centre (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) :
    (GluingDatum.incidentEdges (TripodFrame.centreTarget κ)).card = 3 := by
  have hle := κ.data.incidentEdges_card_le_three_of_changeMinimalAt κ.fullDim.valid
    (TripodFrame.centreTarget κ) (κ.fullDim.changeMinimal _)
  have hcl : (GluingDatum.incidentEdges (TripodFrame.centreTarget κ)).card ≠ 1 :=
    not_isLeafVertex_of_three_le κ.fullDim (centreSource κ) (three_le_centreSource κ)
  have hpos : 0 < (GluingDatum.incidentEdges (TripodFrame.centreTarget κ)).card :=
    Finset.card_pos.mpr ⟨_, lastEdge_mem_centre κ 0⟩
  by_contra h3
  have h2 : (GluingDatum.incidentEdges (TripodFrame.centreTarget κ)).card = 2 := by omega
  obtain ⟨b, hb, hbl⟩ := exists_leaf_of_divalent κ hconn hClaw h2
  exact false_of_divalent_of_leaf κ h2 hb hbl

/-- **The lost edges are the three edges at `φ(c)`** (Theorem 4.7(b)): they are lost
(`isLost_of_centre`), and there are at most three lost edges (`card_le_three_of_isLost`). -/
theorem isLost_iff (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    (t : κ.target.edges) :
    IsLost κ t ↔ t ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ) := by
  classical
  refine ⟨fun ht ↦ ?_, isLost_of_centre κ hClaw⟩
  by_contra hNot
  have hAll : ∀ u ∈ insert t (GluingDatum.incidentEdges (TripodFrame.centreTarget κ)),
      IsLost κ u := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact ht
    · exact isLost_of_centre κ hClaw hu
  have hCard := card_le_three_of_isLost κ _ hAll
  rw [Finset.card_insert_of_notMem hNot, card_incidentEdges_centre κ hconn hClaw] at hCard
  omega

/-- The centre is unramified over the trivalent `φ(c)`. -/
theorem localRamification_centre (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) :
    κ.data.localRamification (centreSource κ).1.1 ⟨(centreSource κ).1.2, (centreSource κ).2⟩ =
      0 :=
  SlopesGeometric.localRamification_eq_zero_of_trivalent_target κ.data κ.fullDim.valid _
    (κ.fullDim.changeMinimal _) (card_incidentEdges_centre κ hconn hClaw) _

/-- **The three last edges lie over three distinct edges** (Part I `prop-local` r0-nd3: `c`
is unramified over the trivalent `c*`, so its three surviving edges do not fit in two directions,
`not_forall_target_mem_pair`). -/
theorem lastEdge_target_injective (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) :
    Function.Injective fun k ↦ (lastEdge κ k).1.1.1 := by
  intro a b hab
  by_contra hne
  obtain ⟨c3, hc3a, hc3b⟩ := fin3_exists_third a b hne
  apply not_forall_target_mem_pair κ.fullDim.danglingEdgeNoGlue (nonDanglingValency_centre κ)
    (localRamification_centre κ hconn hClaw) (lastEdge κ a).1.1.1 (lastEdge κ c3).1.1.1
  intro g hg
  obtain ⟨m, rfl⟩ := exists_eq_lastEdge κ hg
  have hm := fin3_cases a b c3 m hne hc3a hc3b
  rcases hm with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl hab.symm
  · exact Or.inr rfl

/-- The edges at `φ(c)` are the targets of the last edges. -/
theorem mem_centre_iff (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    (t : κ.target.edges) :
    t ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ) ↔
      ∃ k, t = (lastEdge κ k).1.1.1 := by
  classical
  refine ⟨fun ht ↦ ?_, fun ⟨k, hk⟩ ↦ hk ▸ lastEdge_mem_centre κ k⟩
  have hSub : (Finset.univ.image fun k ↦ (lastEdge κ k).1.1.1) ⊆
      GluingDatum.incidentEdges (TripodFrame.centreTarget κ) := by
    intro u hu
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hu
    exact lastEdge_mem_centre κ k
  have hEq := Finset.eq_of_subset_of_card_le hSub (by
    rw [card_incidentEdges_centre κ hconn hClaw,
      Finset.card_image_of_injective _ (lastEdge_target_injective κ hconn hClaw)]
    simp)
  rw [← hEq] at ht
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp ht
  exact ⟨k, hk.symm⟩

/-- **The far end of an edge at `φ(c)` that is not a leaf lies in `T̂`**: it has another edge, not
at `φ(c)` (no parallel edges in a tree), hence not lost (`isLost_iff`), so a G-edge lies over it. -/
theorem far_end_mem_gImage (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    {t : κ.target.edges} (ht : t ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ))
    {x : κ.target.V} (hx : (t : κ.target.V × κ.target.V).1 = x ∨ (t : κ.target.V × κ.target.V).2 = x)
    (hxc : x ≠ TripodFrame.centreTarget κ) (hxl : ¬ IsLeafVertex κ.target x) :
    x ∈ TripodFrame.gImage κ := by
  classical
  have hxt : t ∈ GluingDatum.incidentEdges x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hcard : 1 < (GluingDatum.incidentEdges x).card := by
    have h1 : (GluingDatum.incidentEdges x).card ≠ 1 := hxl
    have h0 : 0 < (GluingDatum.incidentEdges x).card := Finset.card_pos.mpr ⟨t, hxt⟩
    omega
  obtain ⟨g, hg, hgt⟩ := Finset.exists_mem_ne hcard t
  have hgc : g ∉ GluingDatum.incidentEdges (TripodFrame.centreTarget κ) := by
    intro hgc
    exact hgt (TargetGeodesic.eq_of_incident_of_genusZero κ.fullDim.targetConnected
      κ.fullDim.targetGenus hxc (Finset.mem_filter.mp hg).2 (Finset.mem_filter.mp hgc).2 hx
      (Finset.mem_filter.mp ht).2)
  have hgNL : ¬ IsLost κ g := fun h ↦ hgc ((isLost_iff κ hconn hClaw g).mp h)
  unfold IsLost at hgNL
  push Not at hgNL
  obtain ⟨e, hG, he⟩ := hgNL
  exact ⟨e, hG, he ▸ (Finset.mem_filter.mp hg).2⟩

/-- **Two edges at `φ(c)` do not both have their far ends in `T̂`**: cut at the first (it is lost);
`T̂` lies on one side (`iff_of_mem_gImage`), but the first far end is across the cut from `φ(c)`
and the second is not. -/
theorem not_two_far_ends (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    {t u : κ.target.edges} (ht : t ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ))
    (hu : u ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ)) (htu : t ≠ u)
    {x y : κ.target.V}
    (hx : (t : κ.target.V × κ.target.V).1 = x ∨ (t : κ.target.V × κ.target.V).2 = x)
    (hxc : x ≠ TripodFrame.centreTarget κ)
    (hy : (u : κ.target.V × κ.target.V).1 = y ∨ (u : κ.target.V × κ.target.V).2 = y)
    (hyc : y ≠ TripodFrame.centreTarget κ)
    (hxG : x ∈ TripodFrame.gImage κ) (hyG : y ∈ TripodFrame.gImage κ) : False := by
  obtain ⟨A⟩ := TargetGeodesic.exists_treeRank κ.target κ.fullDim.targetConnected
    κ.fullDim.targetGenus
  have hLost := isLost_of_centre κ hClaw ht
  have hG : ∀ a : NonDanglingEdge κ.data, IsGSlot (κ.ident.row a.stablePath) →
      (Below A t (a.1.1.1 : κ.target.V × κ.target.V).1 ↔
        Below A t (a.1.1.1 : κ.target.V × κ.target.V).2) :=
    fun a ha ↦ (below_fst_iff_snd A _ _).mpr (hLost a ha)
  have hxy := iff_of_mem_gImage hconn κ hG hxG hyG
  have h1 : ¬ (Below A t (t : κ.target.V × κ.target.V).1 ↔
      Below A t (t : κ.target.V × κ.target.V).2) := fun h ↦ (below_fst_iff_snd A t t).mp h rfl
  have h2 : Below A t (u : κ.target.V × κ.target.V).1 ↔
      Below A t (u : κ.target.V × κ.target.V).2 := (below_fst_iff_snd A t u).mpr (Ne.symm htu)
  rw [iff_ends hx (Finset.mem_filter.mp ht).2 hxc] at h1
  rw [iff_ends hy (Finset.mem_filter.mp hu).2 hyc] at h2
  exact h1 (hxy.trans h2)

/-- **Exactly one last edge lies over a non-leaf edge** (Theorem 4.7(b)). Two far
ends of non-leaf edges at `φ(c)` would both lie in `T̂` (`far_end_mem_gImage`), which
`not_two_far_ends` forbids. If all three edges at `φ(c)` were leaf edges, `T` would be the star at
`φ(c)` (`exists_incident_of_star`), and the image of a mark, which is neither `φ(c)` (claw) nor a
leaf (it carries a branch vertex), would have nowhere to be. -/
theorem existsUnique_not_leaf (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) :
    ∃! k, ¬ IsLeafEdge κ.target (lastEdge κ k).1.1.1 := by
  have hcl : ¬ IsLeafVertex κ.target (TripodFrame.centreTarget κ) :=
    not_isLeafVertex_of_three_le κ.fullDim (centreSource κ) (three_le_centreSource κ)
  -- uniqueness
  have hUniq : ∀ a b : Fin 3, ¬ IsLeafEdge κ.target (lastEdge κ a).1.1.1 →
      ¬ IsLeafEdge κ.target (lastEdge κ b).1.1.1 → a = b := by
    intro a b ha hb
    by_contra hab
    obtain ⟨x, hx, hxc, -⟩ := exists_far_end (lastEdge_mem_centre κ a)
    obtain ⟨y, hy, hyc, -⟩ := exists_far_end (lastEdge_mem_centre κ b)
    have hxl : ¬ IsLeafVertex κ.target x := fun h ↦ ha (isLeafEdge_of_end hx h)
    have hyl : ¬ IsLeafVertex κ.target y := fun h ↦ hb (isLeafEdge_of_end hy h)
    exact not_two_far_ends κ hconn hClaw (lastEdge_mem_centre κ a) (lastEdge_mem_centre κ b)
      (fun h ↦ hab (lastEdge_target_injective κ hconn hClaw h)) hx hxc hy hyc
      (far_end_mem_gImage κ hconn hClaw (lastEdge_mem_centre κ a) hx hxc hxl)
      (far_end_mem_gImage κ hconn hClaw (lastEdge_mem_centre κ b) hy hyc hyl)
  -- existence
  have hEx : ∃ k, ¬ IsLeafEdge κ.target (lastEdge κ k).1.1.1 := by
    by_contra hNo
    push Not at hNo
    have hTip : ∀ t ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ), ∀ x : κ.target.V,
        ((t : κ.target.V × κ.target.V).1 = x ∨ (t : κ.target.V × κ.target.V).2 = x) →
        x ≠ TripodFrame.centreTarget κ → IsLeafVertex κ.target x := by
      intro t ht x hx hxc
      obtain ⟨k, rfl⟩ := (mem_centre_iff κ hconn hClaw t).mp ht
      exact isLeafVertex_of_isLeafEdge (hNo k) (Finset.mem_filter.mp ht).2 hcl hx hxc
    obtain ⟨t, ht, hm⟩ := exists_incident_of_star κ.fullDim.targetConnected
      ⟨_, lastEdge_mem_centre κ 0⟩ hTip (TripodFrame.markSource κ 0).1.1
    have hmc : (TripodFrame.markSource κ 0).1.1 ≠ TripodFrame.centreTarget κ :=
      fun h ↦ hClaw (h ▸ markTarget_mem_gImage κ 0)
    exact not_isLeafVertex_of_three_le κ.fullDim _ (three_le_markSource κ 0)
      (hTip t ht _ hm hmc)
  obtain ⟨k, hk⟩ := hEx
  exact ⟨k, hk, fun b hb ↦ hUniq b k hb hk⟩

/-- A last edge over a leaf edge has index one. -/
theorem lastEdge_index_of_leaf {k : Fin 3} (h : IsLeafEdge κ.target (lastEdge κ k).1.1.1) :
    κ.data.sourceEdgeIndex (lastEdge κ k).1 = 1 := by
  obtain ⟨v, hv, hvt⟩ := exists_leaf_of_isLeafEdge h
  exact LeafFibre.sourceEdgeIndex_eq_one_above_leaf κ.fullDim hv hvt

/-- **`|c| = 1`** (Theorem 4.7(b)). `r(c) = 0`, so the index form
(`sum_index_nonDanglingIncident`) gives `|ℓ₀| + |ℓ₁| + |ℓ₂| = 2|c| + 1`; two of the `ℓ_k` lie
over leaf edges (`existsUnique_not_leaf`) and have index one, so the third has index
`2|c| - 1 ≤ |c|`, whence `|c| = 1`. -/
theorem blockCard_centre (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) :
    (κ.data.vertexPartition (centreSource κ).1.1).blockCard (centreSource κ).1.2 = 1 := by
  classical
  have hSum := sum_index_nonDanglingIncident κ.fullDim.danglingEdgeNoGlue (centreSource κ)
  rw [nonDanglingIncident_centre,
    Finset.sum_image (fun a _ b _ h ↦ lastEdge_val_injective κ h), nonDanglingValency_centre,
    localRamification_centre κ hconn hClaw, Fin.sum_univ_three] at hSum
  obtain ⟨k0, -, hUniq⟩ := existsUnique_not_leaf κ hconn hClaw
  have hOne : ∀ k, k ≠ k0 → κ.data.sourceEdgeIndex (lastEdge κ k).1 = 1 := fun k hk ↦
    lastEdge_index_of_leaf κ (by by_contra h; exact hk (hUniq k h))
  have hLe : ∀ k, κ.data.sourceEdgeIndex (lastEdge κ k).1 ≤
      (κ.data.vertexPartition (centreSource κ).1.1).blockCard (centreSource κ).1.2 := fun k ↦
    StableLocalProperties.sourceEdgeIndex_le_blockCard κ.data (centreSource κ)
      ⟨(lastEdge κ k).1, lastEdge_incident κ k⟩
  have hPos := (κ.data.vertexPartition (centreSource κ).1.1).blockCard_pos (centreSource κ).1.2
  have h0 := hLe 0
  have h1 := hLe 1
  have h2 := hLe 2
  push_cast at hSum
  fin_cases k0
  · have := hOne 1 (by decide)
    have := hOne 2 (by decide)
    omega
  · have := hOne 0 (by decide)
    have := hOne 2 (by decide)
    omega
  · have := hOne 0 (by decide)
    have := hOne 1 (by decide)
    omega

/-- Every last edge has index one: it is at most `|c| = 1`. -/
theorem lastEdge_index (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) (k : Fin 3) :
    κ.data.sourceEdgeIndex (lastEdge κ k).1 = 1 := by
  have hLe : κ.data.sourceEdgeIndex (lastEdge κ k).1 ≤
      (κ.data.vertexPartition (centreSource κ).1.1).blockCard (centreSource κ).1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard κ.data (centreSource κ)
      ⟨(lastEdge κ k).1, lastEdge_incident κ k⟩
  rw [blockCard_centre κ hconn hClaw] at hLe
  have hPos := GluingDatum.sourceEdgeIndex_pos κ.data (lastEdge κ k).1
  omega

/-- **A leg edge over a leaf edge lies over the last edge's target** (Lemma 4.4 with the claw):
the leaf edge is lost, hence at `c*`, hence the target of some `ℓ_m`; the surviving edges over a
leaf edge lie on one stable path, so `m = k`. -/
theorem leafEdge_eq_of_legEdge (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    {k : Fin 3} (e : NonDanglingEdge κ.data) (he : κ.ident.row e.stablePath = legSlot p k)
    (hLeaf : IsLeafEdge κ.target e.1.1.1) : e.1.1.1 = (lastEdge κ k).1.1.1 := by
  have hLost := isLost_of_leg_isLeafEdge κ k e he hLeaf
  obtain ⟨m, hm⟩ := (mem_centre_iff κ hconn hClaw _).mp ((isLost_iff κ hconn hClaw _).mp hLost)
  have hkm : k = m := leg_eq_of_isLeafEdge κ e (lastEdge κ m) he (lastEdge_row κ m) hLeaf hm.symm
  subst hkm
  exact hm

/-! ## 4.  Pass-once on the legs, and the separation `φ(c) ∈ H_k` -/

section Stretch

variable {target : CFGraph.{0}} {deg : ℕ} {data : GluingDatum target deg}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- For a list with no duplicates, consecutive entries are distinct. -/
theorem isChain_ne_of_nodup' {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.Nodup → l.IsChain R → l.IsChain fun a b ↦ R a b ∧ a ≠ b := by
  intro l
  induction l with
  | nil => intro _ _; exact List.isChain_nil
  | cons a t ih =>
      intro hNodup hChain
      cases t with
      | nil => exact List.isChain_singleton _
      | cons b t' =>
          rw [List.isChain_cons_cons] at hChain ⊢
          refine ⟨⟨hChain.1, ?_⟩, ih (List.Nodup.of_cons hNodup) hChain.2⟩
          intro hEq
          exact (List.nodup_cons.mp hNodup).1 (by rw [hEq]; simp)

/-- **A row stretch away from the leaf edges is target-injective.** A duplicate-free chain of
surviving edges, consecutive ones meeting at a vertex of surviving valency two, none of them over a
leaf edge, entered at a vertex through which it does not continue: every meeting vertex is off the
leaves, so of ramification at most one, and consecutive edges lie over distinct target edges
(`RowWalk.target_ne_of_localRamification_le_one`). So the stretch is a non-backtracking walk of the
target tree (`RowGeodesic.isWalkFrom_of_isChain`), which repeats no edge
(`TargetGeodesic.nodup_of_isWalkFrom_of_genusZero`). -/
theorem nodup_targets_of_stretch (fd : FullDimensionalSourcePresentation data coordinate)
    {l : List data.SourceEdge} {vertex : data.SourceVertex}
    (hNodup : l.Nodup) (hSurv : ∀ e ∈ l, ¬ IsDangling data e)
    (hChain : l.IsChain fun first second ↦ ∃ v : data.SourceVertex,
      Incident data first v ∧ Incident data second v ∧ nonDanglingValency data v = 2)
    (hNotLeaf : ∀ e ∈ l, ¬ IsLeafEdge target e.1.1)
    (hHead : ∀ first ∈ l.head?, Incident data first vertex)
    (hEntry : nonDanglingValency data vertex ≠ 2) :
    (l.map fun e ↦ (e.1.1 : target.edges)).Nodup := by
  have hChain' : l.IsChain fun first second ↦ (∃ meet : data.SourceVertex,
      Incident data first meet ∧ Incident data second meet ∧
        nonDanglingValency data meet = 2) ∧ (first.1.1 : target.edges) ≠ second.1.1 := by
    refine (isChain_ne_of_nodup' hNodup hChain).imp_of_mem_imp ?_
    rintro a b ha hb ⟨⟨meet, hAm, hBm, hV⟩, hne⟩
    refine ⟨⟨meet, hAm, hBm, hV⟩, ?_⟩
    have hmem := ((incident_iff_target_mem_and_rel data a meet).mp hAm).1
    have hcard : 2 ≤ (GluingDatum.incidentEdges meet.1.1).card := by
      have h0 : 0 < (GluingDatum.incidentEdges meet.1.1).card := Finset.card_pos.mpr ⟨_, hmem⟩
      have h1 : (GluingDatum.incidentEdges meet.1.1).card ≠ 1 := fun h1 ↦
        hNotLeaf a ha (isLeafEdge_of_end (Finset.mem_filter.mp hmem).2 h1)
      omega
    exact RowWalk.target_ne_of_localRamification_le_one fd.danglingEdgeNoGlue hV
      (DivalentSourceLocal.localRamification_le_one_of_nonleaf data fd.valid meet
        (fd.changeMinimal _) hcard) (hSurv a ha) hAm (hSurv b hb) hBm hne
  exact TargetGeodesic.nodup_of_isWalkFrom_of_genusZero fd.targetConnected fd.targetGenus
    (RowGeodesic.isWalkFrom_of_isChain l vertex hNodup hSurv hChain' hHead (Or.inl hEntry))

end Stretch

/-- The centre and the mark are distinct source vertices. -/
theorem centreSource_ne_markSource (k : Fin 3) :
    centreSource κ ≠ TripodFrame.markSource κ k := fun h ↦
  centre_ne_tripodMark k (κ.ident.vertex.symm.injective (Subtype.ext h))

/-- **The ends of a leg row** are the centre and the mark, in one of the two orders
(`RowSlotOrientation.branch_incident_eq_endpoint`). -/
theorem legRow_ends (k : Fin 3) :
    (RowPosition.rowVertex κ.fullDim (κ.ident.row.symm (legSlot p k)) 0 = centreSource κ ∧
      RowPosition.rowVertex κ.fullDim (κ.ident.row.symm (legSlot p k))
          (RowWalk.orderedRow κ.fullDim.pathEnds (κ.ident.row.symm (legSlot p k))).length =
        TripodFrame.markSource κ k) ∨
    (RowPosition.rowVertex κ.fullDim (κ.ident.row.symm (legSlot p k)) 0 =
        TripodFrame.markSource κ k ∧
      RowPosition.rowVertex κ.fullDim (κ.ident.row.symm (legSlot p k))
          (RowWalk.orderedRow κ.fullDim.pathEnds (κ.ident.row.symm (legSlot p k))).length =
        centreSource κ) := by
  have hc := RowSlotOrientation.branch_incident_eq_endpoint κ.fullDim
    (κ.ident.row.symm (legSlot p k)) ⟨centreSource κ, three_le_centreSource κ⟩
    (edge := (lastEdge κ k).1)
    ⟨(lastEdge κ k).2, (Equiv.eq_symm_apply _).mpr (lastEdge_row κ k)⟩ (lastEdge_incident κ k)
  have hm := RowSlotOrientation.branch_incident_eq_endpoint κ.fullDim
    (κ.ident.row.symm (legSlot p k)) ⟨TripodFrame.markSource κ k, three_le_markSource κ k⟩
    (edge := (firstEdge κ k).1)
    ⟨(firstEdge κ k).2, (Equiv.eq_symm_apply _).mpr (firstEdge_row κ k)⟩
    (firstEdge_incident κ k)
  have hne := centreSource_ne_markSource κ k
  rcases hc with hc | hc <;> rcases hm with hm | hm
  · exact absurd (congrArg Subtype.val (hc.trans hm.symm)) hne
  · exact Or.inl ⟨(congrArg Subtype.val hc).symm, (congrArg Subtype.val hm).symm⟩
  · exact Or.inr ⟨(congrArg Subtype.val hm).symm, (congrArg Subtype.val hc).symm⟩
  · exact absurd (congrArg Subtype.val (hc.trans hm.symm)) hne

/-- **Pass-once on a detour leg.** If `ℓ_k` lies over a leaf edge `t_v`, the edges of the leg
row over leaf edges are the two leaf survivors over `v` (`leafEdge_eq_of_legEdge`), and they are
the two edges of the ordered row at its centre end: the first is `ℓ_k`, at the centre, and the
second meets it at the leaf fold `A_v`. The rest of the row is a stretch away from the leaf edges,
entered at the mark (`nodup_targets_of_stretch`). -/
theorem legEdge_eq_of_target_eq_of_detour (hconn : core.Connected)
    (hClaw : TripodFrame.IsClaw κ) {k : Fin 3}
    (hDet : IsLeafEdge κ.target (lastEdge κ k).1.1.1)
    (e e' : NonDanglingEdge κ.data) (he : κ.ident.row e.stablePath = legSlot p k)
    (he' : κ.ident.row e'.stablePath = legSlot p k) (hT : e.1.1.1 = e'.1.1.1)
    (hNotLeaf : ¬ IsLeafEdge κ.target e.1.1.1) : e = e' := by
  classical
  obtain ⟨v, hv, hvt⟩ := exists_leaf_of_isLeafEdge hDet
  set L := κ.ident.row.symm (legSlot p k) with hL
  set R := RowWalk.orderedRow κ.fullDim.pathEnds L with hR
  have hNodup : R.Nodup := RowWalk.orderedRow_nodup _ _
  have hChain := RowWalk.orderedRow_chain κ.fullDim.pathEnds L
  have hOnR : ∀ g ∈ R, ∃ hS : ¬ IsDangling κ.data g,
      κ.ident.row (NonDanglingEdge.stablePath ⟨g, hS⟩) = legSlot p k := by
    intro g hg
    obtain ⟨hS, hP⟩ := (RowWalk.mem_orderedRow_iff _ _ _).mp hg
    exact ⟨hS, by rw [hP, hL, Equiv.apply_symm_apply]⟩
  have hMemR : ∀ g : NonDanglingEdge κ.data, κ.ident.row g.stablePath = legSlot p k →
      g.1 ∈ R := fun g hg ↦
    (RowWalk.mem_orderedRow_iff _ _ _).mpr ⟨g.2, (Equiv.eq_symm_apply _).mpr hg⟩
  have hSurvR : ∀ g ∈ R, ¬ IsDangling κ.data g := fun g hg ↦ (hOnR g hg).1
  have hLeafR : ∀ g ∈ R, IsLeafEdge κ.target g.1.1 → g ∈ LeafFibre.leafSurvivors hv := by
    intro g hg hgl
    obtain ⟨hS, hrow⟩ := hOnR g hg
    exact (LeafFibre.mem_leafSurvivors hv).mpr
      ⟨hS, (leafEdge_eq_of_legEdge κ hconn hClaw ⟨g, hS⟩ hrow hgl).trans hvt⟩
  have hSurvLeaf : ∀ g ∈ LeafFibre.leafSurvivors (data := κ.data) hv,
      IsLeafEdge κ.target g.1.1 := fun g hg ↦ by
    rw [((LeafFibre.mem_leafSurvivors hv).mp hg).2]
    exact isLeafEdge_leafEdge hv
  have hℓS : (lastEdge κ k).1 ∈ LeafFibre.leafSurvivors hv :=
    (LeafFibre.mem_leafSurvivors hv).mpr ⟨(lastEdge κ k).2, hvt⟩
  have hℓA := LeafFibre.incident_coreVertex_of_mem_leafSurvivors κ.fullDim hv hℓS
  have hAc : LeafFibre.coreVertex κ.fullDim hv ≠ centreSource κ := by
    intro h
    have hcv : IsLeafVertex κ.target (centreSource κ).1.1 := by
      rw [← h]
      exact hv
    exact not_isLeafVertex_of_three_le κ.fullDim (centreSource κ) (three_le_centreSource κ) hcv
  have hAv : LeafFibre.coreVertex κ.fullDim hv =
      otherEnd κ.data (lastEdge κ k).1 (centreSource κ) :=
    (eq_or_eq_otherEnd κ.data (lastEdge_incident κ k) hℓA).resolve_left hAc
  have hAval := LeafFibre.nonDanglingValency_coreVertex κ.fullDim hv
  have hCard := LeafFibre.leafSurvivors_card κ.fullDim hv
  have hm3 : nonDanglingValency κ.data (TripodFrame.markSource κ k) = 3 :=
    le_antisymm (κ.fullDim.trivalent _) (three_le_markSource κ k)
  have hlen0 : 0 < R.length := RowSlotOrientation.orderedRow_length_pos κ.fullDim L
  -- the leaf survivors are two named edges
  have hPair : ∀ {a b : κ.data.SourceEdge}, a ∈ LeafFibre.leafSurvivors hv →
      b ∈ LeafFibre.leafSurvivors hv → a ≠ b →
      ∀ g ∈ LeafFibre.leafSurvivors (data := κ.data) hv, g = a ∨ g = b := by
    intro a b ha hb hab g hg
    by_contra hNo
    push Not at hNo
    have hsub : ({g, a, b} : Finset κ.data.SourceEdge) ⊆ LeafFibre.leafSurvivors hv := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hg
      · exact ha
      · exact hb
    have hle := Finset.card_le_card hsub
    rw [hCard, Finset.card_insert_of_notMem (by simp [hNo.1, hNo.2]),
      Finset.card_pair hab] at hle
    omega
  -- the stretch, given its properties, finishes the proof
  suffices hW : ∃ W : List κ.data.SourceEdge, W.Nodup ∧ (∀ g ∈ W, ¬ IsDangling κ.data g) ∧
      W.IsChain (fun first second ↦ ∃ x : κ.data.SourceVertex, Incident κ.data first x ∧
        Incident κ.data second x ∧ nonDanglingValency κ.data x = 2) ∧
      (∀ g ∈ W, ¬ IsLeafEdge κ.target g.1.1) ∧
      (∀ first ∈ W.head?, Incident κ.data first (TripodFrame.markSource κ k)) ∧
      (∀ g ∈ R, ¬ IsLeafEdge κ.target g.1.1 → g ∈ W) by
    obtain ⟨W, h1, h2, h3, h4, h5, h6⟩ := hW
    have hNd := nodup_targets_of_stretch κ.fullDim h1 h2 h3 h4 h5 (by rw [hm3]; decide)
    exact Subtype.ext (List.inj_on_of_nodup_map hNd (h6 e.1 (hMemR e he) hNotLeaf)
      (h6 e'.1 (hMemR e' he') (hT ▸ hNotLeaf)) hT)
  rcases legRow_ends κ k with ⟨h0, hlen⟩ | ⟨h0, hlen⟩
  · -- the row starts at the centre: its first two edges are the leaf survivors
    have hR0 : R[0] = (lastEdge κ k).1 := by
      have hI : Incident κ.data R[0] (centreSource κ) :=
        h0 ▸ RowPosition.rowVertex_incident κ.fullDim L hlen0
      obtain ⟨hS, hrow⟩ := hOnR _ (List.getElem_mem hlen0)
      exact congrArg Subtype.val (lastEdge_unique κ k (g := ⟨R[0], hS⟩) hI hrow)
    have hrv1 : RowPosition.rowVertex κ.fullDim L 1 = LeafFibre.coreVertex κ.fullDim hv := by
      have h := OrientedTraversal.walkVertex_succ (data := κ.data) R
        (RowWalk.startVertex κ.fullDim.pathEnds L) hlen0
      change RowPosition.rowVertex κ.fullDim L 1 =
        otherEnd κ.data R[0] (RowPosition.rowVertex κ.fullDim L 0) at h
      rw [h, hR0, h0, hAv]
    have hlen2 : 1 < R.length := by
      by_contra hlt
      have hl1 : R.length = 1 := by omega
      have hmk := hlen
      rw [hl1, hrv1] at hmk
      have h3 := three_le_markSource κ k
      rw [← hmk, hAval] at h3
      omega
    have hR1 : R[1] ∈ LeafFibre.leafSurvivors hv :=
      LeafFibre.mem_leafSurvivors_of_incident_coreVertex κ.fullDim hv
        (hSurvR _ (List.getElem_mem hlen2))
        (hrv1 ▸ RowPosition.rowVertex_incident κ.fullDim L hlen2)
    have hR01 : R[0] ≠ R[1] := fun h ↦ absurd (hNodup.getElem_inj_iff.mp h) (by omega)
    have hSet := hPair (hR0 ▸ hℓS) hR1 hR01
    refine ⟨(R.drop 2).reverse, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact List.nodup_reverse.mpr (hNodup.sublist (List.drop_sublist _ _))
    · intro g hg
      exact hSurvR g (List.mem_of_mem_drop (List.mem_reverse.mp hg))
    · rw [List.isChain_reverse]
      exact (hChain.drop 2).imp fun a b ⟨x, ha, hb, hx⟩ ↦ ⟨x, hb, ha, hx⟩
    · intro g hg hgl
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp (List.mem_reverse.mp hg)
      rcases hSet _ (hLeafR _ (List.getElem_mem _) hgl) with h | h
      · have := hNodup.getElem_inj_iff.mp h
        omega
      · have := hNodup.getElem_inj_iff.mp h
        omega
    · intro first hfirst
      rw [List.head?_reverse, List.getLast?_drop] at hfirst
      split_ifs at hfirst with hle
      · simp at hfirst
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hfirst
      rw [← (Option.some.inj hfirst), ← hlen]
      have hI := (OrientedTraversal.walkVertex_succ_incident (data := κ.data) (row := R)
        (start := RowWalk.startVertex κ.fullDim.pathEnds L) (j := R.length - 1) (by omega))
      have hLen : R.length - 1 + 1 = R.length := by omega
      rw [hLen] at hI
      exact hI
    · intro g hg hgl
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      have hj2 : 2 ≤ j := by
        by_contra hlt
        have hj01 : j = 0 ∨ j = 1 := by omega
        rcases hj01 with rfl | rfl
        · exact hgl (hSurvLeaf _ (hR0 ▸ hℓS))
        · exact hgl (hSurvLeaf _ hR1)
      exact List.mem_reverse.mpr (List.mem_drop_iff_getElem.mpr
        ⟨j - 2, by omega, by congr 1; omega⟩)
  · -- the row starts at the mark: its last two edges are the leaf survivors
    have hIlast : ∀ j, (hj : j < R.length) →
        Incident κ.data R[j] (RowPosition.rowVertex κ.fullDim L (j + 1)) := fun j hj ↦
      OrientedTraversal.walkVertex_succ_incident (data := κ.data) (row := R)
        (start := RowWalk.startVertex κ.fullDim.pathEnds L) hj
    have hRl : R[R.length - 1] = (lastEdge κ k).1 := by
      have hI := hIlast (R.length - 1) (by omega)
      rw [show R.length - 1 + 1 = R.length by omega, hlen] at hI
      obtain ⟨hS, hrow⟩ := hOnR _ (List.getElem_mem (show R.length - 1 < R.length by omega))
      exact congrArg Subtype.val (lastEdge_unique κ k (g := ⟨_, hS⟩) hI hrow)
    have hrv : RowPosition.rowVertex κ.fullDim L (R.length - 1) =
        LeafFibre.coreVertex κ.fullDim hv := by
      have hI := RowPosition.rowVertex_incident κ.fullDim L
        (show R.length - 1 < R.length by omega)
      rw [hRl] at hI
      have hne : RowPosition.rowVertex κ.fullDim L (R.length - 1) ≠ centreSource κ := by
        rw [← hlen]
        have h := OrientedTraversal.walkVertex_ne_succ (data := κ.data) (row := R)
          (start := RowWalk.startVertex κ.fullDim.pathEnds L) (j := R.length - 1) (by omega)
        rw [show R.length - 1 + 1 = R.length by omega] at h
        exact fun h' ↦ h h'.symm
      rcases eq_or_eq_otherEnd κ.data (lastEdge_incident κ k) hI with h | h
      · exact absurd h hne
      · rw [h, ← hAv]
    have hlen2 : 1 < R.length := by
      by_contra hlt
      have hl1 : R.length = 1 := by omega
      have hmk := hrv
      rw [hl1] at hmk
      change RowPosition.rowVertex κ.fullDim L 0 = _ at hmk
      rw [h0] at hmk
      have h3 := three_le_markSource κ k
      rw [hmk, hAval] at h3
      omega
    have hR2 : R[R.length - 2] ∈ LeafFibre.leafSurvivors hv := by
      have hI := hIlast (R.length - 2) (by omega)
      rw [show R.length - 2 + 1 = R.length - 1 by omega, hrv] at hI
      exact LeafFibre.mem_leafSurvivors_of_incident_coreVertex κ.fullDim hv
        (hSurvR _ (List.getElem_mem _)) hI
    have hR21 : R[R.length - 1] ≠ R[R.length - 2] := fun h ↦
      absurd (hNodup.getElem_inj_iff.mp h) (by omega)
    have hSet := hPair (hRl ▸ hℓS) hR2 hR21
    refine ⟨R.take (R.length - 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hNodup.sublist (List.take_sublist _ _)
    · intro g hg
      exact hSurvR g (List.mem_of_mem_take hg)
    · exact hChain.take _
    · intro g hg hgl
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hg
      rcases hSet _ (hLeafR _ (List.getElem_mem _) hgl) with h | h
      · have := hNodup.getElem_inj_iff.mp h
        omega
      · have := hNodup.getElem_inj_iff.mp h
        omega
    · intro first hfirst
      rw [List.head?_take] at hfirst
      split_ifs at hfirst with hle
      · simp at hfirst
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen0] at hfirst
      rw [← (Option.some.inj hfirst), ← h0]
      exact RowPosition.rowVertex_incident κ.fullDim L hlen0
    · intro g hg hgl
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      have hj2 : j < R.length - 2 := by
        by_contra hlt
        have hj01 : j = R.length - 1 ∨ j = R.length - 2 := by omega
        rcases hj01 with h | h
        · exact hgl (by simp only [h]; exact hSurvLeaf _ (hRl ▸ hℓS))
        · exact hgl (by simp only [h]; exact hSurvLeaf _ hR2)
      exact List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩

/-- **Pass-once on the legs of a claw frame** (Lemma 4.2): two surviving edges of leg `k`
over one target edge that is not a leaf edge are equal. A leg whose last edge lies over the non-leaf
edge at `φ(c)` has no leaf detour (`leafEdge_eq_of_legEdge`), and
`legEdge_injective_of_noDetour` applies; otherwise `legEdge_eq_of_target_eq_of_detour`. -/
theorem legEdge_eq_of_target_eq (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    {k : Fin 3} (e e' : NonDanglingEdge κ.data) (he : κ.ident.row e.stablePath = legSlot p k)
    (he' : κ.ident.row e'.stablePath = legSlot p k) (hT : e.1.1.1 = e'.1.1.1)
    (hNotLeaf : ¬ IsLeafEdge κ.target e.1.1.1) : e = e' := by
  by_cases hDet : IsLeafEdge κ.target (lastEdge κ k).1.1.1
  · exact legEdge_eq_of_target_eq_of_detour κ hconn hClaw hDet e e' he he' hT hNotLeaf
  · have hNo : ¬ HasDetour κ k := by
      rintro ⟨g, hg, hgl⟩
      exact hDet (leafEdge_eq_of_legEdge κ hconn hClaw g hg hgl ▸ hgl)
    exact legEdge_injective_of_noDetour κ k hNo e e' he he' hT

/-- The first edge of a leg does not lie over a leaf edge: a leaf edge under a leg lies at `φ(c)`
(`leafEdge_eq_of_legEdge`), so its ends would be `φ(c)` and `φ(k)`, neither of which is a leaf. -/
theorem firstEdge_not_leaf (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    (k : Fin 3) : ¬ IsLeafEdge κ.target (firstEdge κ k).1.1.1 := by
  intro hLeaf
  have ht := leafEdge_eq_of_legEdge κ hconn hClaw (firstEdge κ k) (firstEdge_row κ k) hLeaf
  have hc : ((firstEdge κ k).1.1.1 : κ.target.V × κ.target.V).1 = TripodFrame.centreTarget κ ∨
      ((firstEdge κ k).1.1.1 : κ.target.V × κ.target.V).2 = TripodFrame.centreTarget κ := by
    rw [ht]
    exact (Finset.mem_filter.mp (lastEdge_mem_centre κ k)).2
  have hm := incident_target (firstEdge_incident κ k)
  have hmc : (TripodFrame.markSource κ k).1.1 ≠ TripodFrame.centreTarget κ :=
    fun h ↦ hClaw (h ▸ markTarget_mem_gImage κ k)
  have hcl := vertex_degree_ne_one_of_three_le κ.fullDim (centreSource κ) (three_le_centreSource κ)
  have hml := vertex_degree_ne_one_of_three_le κ.fullDim _ (three_le_markSource κ k)
  unfold IsLeafEdge at hLeaf
  rcases hc with h1 | h1 <;> rcases hm with h2 | h2
  · exact hmc (h2.symm.trans h1)
  · rcases hLeaf with h3 | h3
    · rw [h1] at h3
      exact hcl h3
    · rw [h2] at h3
      exact hml h3
  · rcases hLeaf with h3 | h3
    · rw [h2] at h3
      exact hml h3
    · rw [h1] at h3
      exact hcl h3
  · exact hmc (h2.symm.trans h1)

/-- **`φ(c) ∈ H_k`** (Theorem 4.7(b), Corollary 4.3): the target edge `h_k` under the first
edge of leg `k` separates `φ(c)` from `φ(k)`. The first edge is the only leg edge over `h_k`
(pass-once, `h_k` not being a leaf edge), so the leg crosses the cut at `h_k` once and its two
ends lie on opposite sides (`markSource_iff_not_centreSource`). -/
theorem firstEdge_separates (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) (k : Fin 3) :
    TreeMetricPotential.cutValue (firstEdge κ k).1.1.1 (TripodFrame.centreTarget κ) ≠
      TreeMetricPotential.cutValue (firstEdge κ k).1.1.1 (TripodFrame.markSource κ k).1.1 := by
  have hConn := κ.fullDim.targetConnected
  have hGenus := κ.fullDim.targetGenus
  set h := (firstEdge κ k).1.1.1 with hh
  let Q : κ.target.V → Prop := fun x ↦ TreeMetricPotential.cutValue h x = 0
  have hQe : ¬ (Q (h : κ.target.V × κ.target.V).1 ↔ Q (h : κ.target.V × κ.target.V).2) := by
    simp only [Q, TreeMetricPotential.cutValue_tail, TreeMetricPotential.cutValue_head hConn hGenus]
    norm_num
  have hOther : ∀ a : NonDanglingEdge κ.data, κ.ident.row a.stablePath = legSlot p k →
      a ≠ firstEdge κ k →
      (Q (a.1.1.1 : κ.target.V × κ.target.V).1 ↔ Q (a.1.1.1 : κ.target.V × κ.target.V).2) := by
    intro a ha hne
    have hah : h ≠ a.1.1.1 := by
      intro heq
      refine hne (legEdge_eq_of_target_eq κ hconn hClaw a (firstEdge κ k) ha (firstEdge_row κ k)
        heq.symm ?_)
      rw [← heq]
      exact firstEdge_not_leaf κ hconn hClaw k
    simp only [Q, TreeMetricPotential.cutValue_other hConn hGenus h a.1.1.1 hah]
  have hSide := markSource_iff_not_centreSource κ k Q (firstEdge κ k) (firstEdge_row κ k) hQe
    hOther
  intro heq
  have hcm : Q (centreSource κ).1.1 ↔ Q (TripodFrame.markSource κ k).1.1 := by
    show TreeMetricPotential.cutValue h (TripodFrame.centreTarget κ) = 0 ↔ _
    rw [heq]
  by_cases hq : Q (TripodFrame.markSource κ k).1.1
  · exact (hSide.mp hq) (hcm.mpr hq)
  · exact hq (hSide.mpr fun hc ↦ hq (hcm.mp hc))

/-! ## 5.  Leg indices: every leg edge has index one (Lemma 4.8) -/

/-- **Pairing at a divalent vertex, one row at a time** (§4.4, Pairing; Part I
`lemma-change-zero`). At a divalent target vertex `u` with edges `a ≠ b`, if every surviving edge
of the row `r` over an edge at `u` has an unramified block over `u`, then the columns `a` and `b`
agree in the row `r`: such a block is one sheet-block of each edge partition at `u`, so
`f ↦ sourceEdge b f.sheet` is an index-preserving bijection of the row's fibres over `a` and `b`
(the row-by-row form of
`StableLocalProperties.matrix_column_eq_of_divalent_of_surviving_localRamification_zero`). -/
theorem matrix_eq_of_divalent_of_row {u : κ.target.V}
    (hDiv : (GluingDatum.incidentEdges u).card = 2) {a b : κ.target.edges} (hab : a ≠ b)
    (ha : a ∈ GluingDatum.incidentEdges u) (hb : b ∈ GluingDatum.incidentEdges u)
    (r : Fin (p + 1 + 1 + 1 + 3))
    (hRow : ∀ (f : κ.data.SourceEdge) (hS : ¬ IsDangling κ.data f),
      κ.fullDim.labelling.row (NonDanglingEdge.stablePath ⟨f, hS⟩) = r →
      f.1.1 ∈ GluingDatum.incidentEdges u →
      κ.data.localRamification u ((κ.data.vertexPartition u).toBlock f.1.2) = 0) :
    κ.matrix r (κ.fullDim.labelling.targetEdge.symm a) =
      κ.matrix r (κ.fullDim.labelling.targetEdge.symm b) := by
  classical
  unfold Frame.matrix
  rw [LeafFibre.matrix_eq_sum_fibre, LeafFibre.matrix_eq_sum_fibre]
  have hTo : ∀ {one two : κ.target.edges}, one ∈ GluingDatum.incidentEdges u →
      two ∈ GluingDatum.incidentEdges u → one ≠ two →
      ∀ f ∈ LeafFibre.rowFibre κ.fullDim.labelling r one,
        κ.data.sourceEdge two f.1.2 ∈ LeafFibre.rowFibre κ.fullDim.labelling r two ∧
        κ.data.sourceEdge one (κ.data.sourceEdge two f.1.2).1.2 = f ∧
        κ.data.sourceEdgeIndex (κ.data.sourceEdge two f.1.2) = κ.data.sourceEdgeIndex f := by
    intro one two hOne hTwo hOneTwo f hf
    obtain ⟨⟨hS, hR⟩, hT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hf
    have hZero := hRow f hS hR (by rw [hT]; exact hOne)
    have hSelf : κ.data.sourceEdge one f.1.2 = f := by
      rw [← hT]
      exact GluingDatum.sourceEdge_self κ.data f
    have hOneS : ¬ IsDangling κ.data (κ.data.sourceEdge one f.1.2) := by
      rw [hSelf]
      exact hS
    have hTwoS : ¬ IsDangling κ.data (κ.data.sourceEdge two f.1.2) := fun hD ↦
      hOneS ((StableLocalProperties.isDangling_sourceEdge_iff_of_divalent_localRamification_zero
        κ.data u hDiv f.1.2 hZero hOneTwo hOne hTwo).2 hD)
    have hPath := StableLocalProperties.stablePath_sourceEdge_eq_of_divalent_localRamification_zero
      κ.data u hDiv f.1.2 hZero hOneTwo hOne hTwo hOneS hTwoS
    refine ⟨(LeafFibre.mem_rowFibre _ _ _ _).mpr ⟨⟨hTwoS, ?_⟩, rfl⟩, ?_, ?_⟩
    · rw [← hPath, show (⟨κ.data.sourceEdge one f.1.2, hOneS⟩ : NonDanglingEdge κ.data) =
        ⟨f, hS⟩ from Subtype.ext hSelf]
      exact hR
    · exact StableLocalProperties.sourceEdge_transport_left_inverse_of_divalent_localRamification_zero
        κ.data u hDiv one two hOne hTwo f hT hZero
    · have h1 := StableLocalProperties.sourceEdgeIndex_eq_of_divalent_localRamification_zero
        κ.data u hDiv f.1.2 hZero one hOne
      rw [hSelf] at h1
      rw [h1, StableLocalProperties.sourceEdgeIndex_eq_of_divalent_localRamification_zero
        κ.data u hDiv f.1.2 hZero two hTwo]
  refine Finset.sum_nbij' (fun f ↦ κ.data.sourceEdge b f.1.2) (fun f ↦ κ.data.sourceEdge a f.1.2)
    (fun f hf ↦ (hTo ha hb hab f hf).1) (fun f hf ↦ (hTo hb ha (Ne.symm hab) f hf).1)
    (fun f hf ↦ (hTo ha hb hab f hf).2.1) (fun f hf ↦ (hTo hb ha (Ne.symm hab) f hf).2.1) ?_
  intro f hf
  rw [(hTo ha hb hab f hf).2.2]

/-- **Leg indices, the local step** (Lemma 4.8): the index does not change along a leg. Two
consecutive edges `f, g` of leg `k` meet at a vertex `A` of surviving valency two. Over a leaf `g` has index
one. Otherwise, if `|g| ≠ 1 = |f|`, the index form `|f| + |g| = 2|A| - r(A)` with `|g| ≤ |A|`
forces `r(A) = 1`, so `u = φ(A)` is divalent (`ch(u) = 3 - val(u)`) and every other block over `u`
is unramified. The two columns at `u` then agree on every G-row (`matrix_eq_of_divalent_of_row`: a
G-row edge over an edge at `u` does not meet `A`, whose surviving edges are `f` and `g`), and at most
one of them is lost, since two edges at the divalent `u` cannot both reach `φ(c)`. The column trick
`false_of_matrix_eq` forbids this. -/
theorem index_step (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) {k : Fin 3}
    {f g : NonDanglingEdge κ.data} (hfg : Consecutive κ.data f g)
    (hf : κ.ident.row f.stablePath = legSlot p k) (hf1 : κ.data.sourceEdgeIndex f.1 = 1) :
    κ.data.sourceEdgeIndex g.1 = 1 := by
  classical
  obtain ⟨hne, A, hfA, hgA, hA2⟩ := hfg
  have hg : κ.ident.row g.stablePath = legSlot p k := by
    rw [← stablePath_eq_of_consecutive ⟨hne, A, hfA, hgA, hA2⟩]
    exact hf
  have hgu := ((incident_iff_target_mem_and_rel κ.data g.1 A).mp hgA).1
  by_cases hLeafU : IsLeafVertex κ.target A.1.1
  · exact LeafFibre.sourceEdgeIndex_eq_one_above_leaf κ.fullDim hLeafU
      (eq_leafEdge_of_mem hLeafU hgu)
  have hcard : 2 ≤ (GluingDatum.incidentEdges A.1.1).card := by
    have h0 : 0 < (GluingDatum.incidentEdges A.1.1).card := Finset.card_pos.mpr ⟨_, hgu⟩
    have h1 : (GluingDatum.incidentEdges A.1.1).card ≠ 1 := hLeafU
    omega
  have hr1 := DivalentSourceLocal.localRamification_le_one_of_nonleaf κ.data κ.fullDim.valid A
    (κ.fullDim.changeMinimal _) hcard
  have hr0 := κ.data.localRamification_nonneg A.1.1 (κ.fullDim.valid.2 _) ⟨A.1.2, A.2⟩
  have hfgne : f.1 ≠ g.1 := fun h ↦ hne (Subtype.ext h)
  have hPair : nonDanglingIncident κ.data A = {f.1, g.1} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hfA⟩
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨g.2, hgA⟩
    · rw [card_nonDanglingIncident, hA2, Finset.card_pair hfgne]
  have hSum := sum_index_nonDanglingIncident κ.fullDim.danglingEdgeNoGlue A
  rw [hPair, Finset.sum_pair hfgne, hA2, hf1] at hSum
  have hgLe : κ.data.sourceEdgeIndex g.1 ≤ (κ.data.vertexPartition A.1.1).blockCard A.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard κ.data A ⟨g.1, hgA⟩
  have hgPos := GluingDatum.sourceEdgeIndex_pos κ.data g.1
  by_contra hg1
  have hrA : κ.data.localRamification A.1.1 ⟨A.1.2, A.2⟩ = 1 := by
    push_cast at hSum
    omega
  -- `u = φ(A)` is divalent and `A` carries all its change
  have hch := IndexPattern.localRamification_le_targetChange κ.fullDim (wall := A.1.1)
    ⟨A.1.2, A.2⟩
  rw [IndexPattern.targetChange_eq_three_sub_valency κ.fullDim] at hch
  have hDiv : (GluingDatum.incidentEdges A.1.1).card = 2 := by omega
  have hChange : κ.data.targetChange A.1.1 = 1 := by
    rw [IndexPattern.targetChange_eq_three_sub_valency κ.fullDim, hDiv]
    norm_num
  have hOthers : ∀ block : (κ.data.vertexPartition A.1.1).Blocks, block ≠ ⟨A.1.2, A.2⟩ →
      κ.data.localRamification A.1.1 block = 0 := by
    intro block hNe
    have hNonneg : ∀ b : (κ.data.vertexPartition A.1.1).Blocks,
        0 ≤ κ.data.localRamification A.1.1 b := fun b ↦
      κ.data.localRamification_nonneg A.1.1 (κ.fullDim.valid.2 _) b
    have hSplit := Finset.sum_erase_add
      (Finset.univ : Finset (κ.data.vertexPartition A.1.1).Blocks)
      (fun b ↦ κ.data.localRamification A.1.1 b)
      (Finset.mem_univ (⟨A.1.2, A.2⟩ : (κ.data.vertexPartition A.1.1).Blocks))
    have hEraseSum : (∑ b ∈ (Finset.univ :
        Finset (κ.data.vertexPartition A.1.1).Blocks).erase ⟨A.1.2, A.2⟩,
        κ.data.localRamification A.1.1 b) = 0 := by
      have hTot : (∑ b : (κ.data.vertexPartition A.1.1).Blocks,
          κ.data.localRamification A.1.1 b) = 1 := hChange
      rw [hrA] at hSplit
      omega
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ hNonneg b)).mp hEraseSum block
      (Finset.mem_erase.mpr ⟨hNe, Finset.mem_univ _⟩)
  -- the two edges at `u`
  obtain ⟨u₁, u₂, hu12, hU⟩ := Finset.card_eq_two.mp hDiv
  have hu₁ : u₁ ∈ GluingDatum.incidentEdges A.1.1 := by rw [hU]; simp
  have hu₂ : u₂ ∈ GluingDatum.incidentEdges A.1.1 := by rw [hU]; simp
  have huc : A.1.1 ≠ TripodFrame.centreTarget κ := by
    intro h
    have h3 := card_incidentEdges_centre κ hconn hClaw
    rw [← h, hDiv] at h3
    omega
  have hNotBoth : ¬ (u₁ ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ) ∧
      u₂ ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ)) := by
    rintro ⟨h1, h2⟩
    exact hu12 (TargetGeodesic.eq_of_incident_of_genusZero κ.fullDim.targetConnected
      κ.fullDim.targetGenus huc (Finset.mem_filter.mp hu₁).2 (Finset.mem_filter.mp h1).2
      (Finset.mem_filter.mp hu₂).2 (Finset.mem_filter.mp h2).2)
  -- the columns at `u` agree on the G-rows
  have hCols : ∀ r, IsGSlot (κ.slot r) →
      κ.matrix r (κ.fullDim.labelling.targetEdge.symm u₁) =
        κ.matrix r (κ.fullDim.labelling.targetEdge.symm u₂) := by
    intro r hr
    refine matrix_eq_of_divalent_of_row κ hDiv hu12 hu₁ hu₂ r ?_
    intro f' hS hRow hf'u
    apply hOthers
    intro hEq
    have hRepr : (κ.data.vertexPartition A.1.1).repr f'.1.2 = A.1.2 := congrArg Subtype.val hEq
    have hInc : Incident κ.data f' A := by
      refine (incident_iff_target_mem_and_rel κ.data f' A).mpr ⟨hf'u, ?_⟩
      show (κ.data.vertexPartition A.1.1).repr A.1.2 = (κ.data.vertexPartition A.1.1).repr f'.1.2
      rw [hRepr, A.2]
    have hmem : f' ∈ nonDanglingIncident κ.data A := (mem_nonDanglingIncident _ _ _).mpr ⟨hS, hInc⟩
    rw [hPair] at hmem
    have hrowk : κ.ident.row (NonDanglingEdge.stablePath ⟨f', hS⟩) = legSlot p k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · rw [show (⟨f', hS⟩ : NonDanglingEdge κ.data) = f from Subtype.ext h]
        exact hf
      · rw [show (⟨f', hS⟩ : NonDanglingEdge κ.data) = g from Subtype.ext h]
        exact hg
    have hslot : κ.slot r = κ.ident.row (NonDanglingEdge.stablePath ⟨f', hS⟩) :=
      ((ident_row_eq_slot κ ⟨f', hS⟩).trans (congrArg κ.slot hRow)).symm
    rw [hslot, hrowk] at hr
    exact legSlot_not_isGSlot k hr
  -- the column trick
  have hLam : ∀ j, IsLost κ ((fun j ↦ (lastEdge κ j).1.1.1) j) := fun j ↦
    isLost_of_centre κ hClaw (lastEdge_mem_centre κ j)
  have hInj := lastEdge_target_injective κ hconn hClaw
  by_cases h1 : u₁ ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ)
  · have h2 : u₂ ∉ GluingDatum.incidentEdges (TripodFrame.centreTarget κ) := fun h2 ↦
      hNotBoth ⟨h1, h2⟩
    exact false_of_matrix_eq κ _ hInj hLam (a := u₂) (b := u₁)
      (fun j h ↦ h2 (h ▸ lastEdge_mem_centre κ j)) (Ne.symm hu12) fun r hr ↦ (hCols r hr).symm
  · exact false_of_matrix_eq κ _ hInj hLam (a := u₁) (b := u₂)
      (fun j h ↦ h1 (h ▸ lastEdge_mem_centre κ j)) hu12 hCols

/-- **Leg indices** (Lemma 4.8): every surviving edge of every leg has index one. The index is constant
along the stable path of the leg (`index_step`, propagated by `eqvGen_iff_of_closed`), and it is one
at the last edge (`lastEdge_index`). -/
theorem legEdge_index (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) {k : Fin 3}
    (e : NonDanglingEdge κ.data) (he : κ.ident.row e.stablePath = legSlot p k) :
    κ.data.sourceEdgeIndex e.1 = 1 := by
  have hClosed : ∀ f g : NonDanglingEdge κ.data, Consecutive κ.data f g →
      (κ.ident.row f.stablePath = legSlot p k ∧ κ.data.sourceEdgeIndex f.1 = 1) →
      (κ.ident.row g.stablePath = legSlot p k ∧ κ.data.sourceEdgeIndex g.1 = 1) := by
    rintro f g hfg ⟨hf, hf1⟩
    refine ⟨?_, index_step κ hconn hClaw hfg hf hf1⟩
    rw [← stablePath_eq_of_consecutive hfg]
    exact hf
  have hEqv : Relation.EqvGen (Consecutive κ.data) (lastEdge κ k) e :=
    (stablePath_eq_iff _ _).mp (κ.ident.row.injective ((lastEdge_row κ k).trans he.symm))
  exact ((eqvGen_iff_of_closed hClosed hEqv).mp
    ⟨lastEdge_row κ k, lastEdge_index κ hconn hClaw k⟩).2

theorem firstEdge_index (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) (k : Fin 3) :
    κ.data.sourceEdgeIndex (firstEdge κ k).1 = 1 :=
  legEdge_index κ hconn hClaw (firstEdge κ k) (firstEdge_row κ k)

/-! ## 6.  `k₀ = 0`: the tripod part of the fibre over `φ(c)` -/

/-- **A surviving vertex on the tripod `Y`**: the centre, or a vertex of surviving valency two on
a leg row. (`RealisationProof.OnTripod` is this predicate, read through the interior addresses.) -/
def YCore (v : κ.data.SourceVertex) : Prop :=
  v = centreSource κ ∨ (nonDanglingValency κ.data v = 2 ∧
    ∃ e : NonDanglingEdge κ.data, Incident κ.data e.1 v ∧ ¬ IsGSlot (κ.ident.row e.stablePath))

/-- A source vertex over `φ(c)` that retracts onto a surviving vertex of the tripod. -/
def OverCentreY (v : κ.data.SourceVertex) : Prop :=
  v.1.1 = TripodFrame.centreTarget κ ∧ ∃ w : κ.data.SourceVertex,
    0 < nonDanglingValency κ.data w ∧ YCore κ w ∧
      PendantRetraction.retractVertex v = PendantRetraction.retractVertex w

/-! ### The tripod vertices over `φ(c)` -/

/-- Two edges at `φ(c)` that are not leaf edges are equal (`existsUnique_not_leaf`). -/
theorem eq_of_not_leaf_centre (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    {t t' : κ.target.edges} (ht : t ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ))
    (ht' : t' ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ))
    (hl : ¬ IsLeafEdge κ.target t) (hl' : ¬ IsLeafEdge κ.target t') : t = t' := by
  obtain ⟨k, rfl⟩ := (mem_centre_iff κ hconn hClaw t).mp ht
  obtain ⟨k', rfl⟩ := (mem_centre_iff κ hconn hClaw t').mp ht'
  obtain ⟨k0, -, hU⟩ := existsUnique_not_leaf κ hconn hClaw
  rw [hU k hl, hU k' hl']

/-- **A leg vertex over `φ(c)`** (surviving valency two, on leg `m`): leg `m` is a detour leg, the
vertex meets a surviving edge over the leaf edge under `ℓ_m` other than `ℓ_m`, and it is a single
sheet. Its two surviving edges lie over two distinct edges at `φ(c)` (`r = 0`), so one of them over
a leaf edge, which is the target of `ℓ_m` (`leafEdge_eq_of_legEdge`); that edge is not `ℓ_m`,
whose ends are the centre and the leaf fold. -/
theorem legVertex_centre (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    {w : κ.data.SourceVertex} (hw2 : nonDanglingValency κ.data w = 2)
    (hwc : w.1.1 = TripodFrame.centreTarget κ) {m : Fin 3} (e : NonDanglingEdge κ.data)
    (hew : Incident κ.data e.1 w) (hem : κ.ident.row e.stablePath = legSlot p m) :
    IsLeafEdge κ.target (lastEdge κ m).1.1.1 ∧
      (∃ y : κ.data.SourceEdge, ¬ IsDangling κ.data y ∧ Incident κ.data y w ∧
        y.1.1 = (lastEdge κ m).1.1.1 ∧ y ≠ (lastEdge κ m).1) ∧
      (κ.data.vertexPartition w.1.1).blockCard w.1.2 = 1 := by
  classical
  set e₂ := stepEdge κ.data hw2 e.1 with he₂
  have he₂S := stepEdge_not_dangling κ.data hw2 e.1
  have he₂I := stepEdge_incident κ.data hw2 e.1
  have he₂ne := stepEdge_ne κ.data hw2 e.1
  have hCons : Consecutive κ.data e ⟨e₂, he₂S⟩ :=
    ⟨fun h ↦ he₂ne (congrArg Subtype.val h).symm, w, hew, he₂I, hw2⟩
  have he₂m : κ.ident.row (NonDanglingEdge.stablePath ⟨e₂, he₂S⟩) = legSlot p m := by
    rw [← stablePath_eq_of_consecutive hCons]
    exact hem
  have hr0 : κ.data.localRamification w.1.1 ⟨w.1.2, w.2⟩ = 0 :=
    SlopesGeometric.localRamification_eq_zero_of_trivalent_target κ.data κ.fullDim.valid _
      (κ.fullDim.changeMinimal _) (by rw [hwc]; exact card_incidentEdges_centre κ hconn hClaw) _
  have hTne := RowWalk.target_ne_of_localRamification_le_one κ.fullDim.danglingEdgeNoGlue hw2
    (by rw [hr0]; norm_num) e.2 hew he₂S he₂I (Ne.symm he₂ne)
  have hmem : ∀ g : κ.data.SourceEdge, Incident κ.data g w →
      g.1.1 ∈ GluingDatum.incidentEdges (TripodFrame.centreTarget κ) := fun g hg ↦ by
    rw [← hwc]
    exact ((incident_iff_target_mem_and_rel κ.data g w).mp hg).1
  -- one of the two edges lies over a leaf edge
  have hOne : ∃ g : NonDanglingEdge κ.data, Incident κ.data g.1 w ∧
      κ.ident.row g.stablePath = legSlot p m ∧ IsLeafEdge κ.target g.1.1.1 := by
    by_contra hNo
    push Not at hNo
    exact hTne (eq_of_not_leaf_centre κ hconn hClaw (hmem _ hew) (hmem _ he₂I)
      (hNo e hew hem) (hNo ⟨e₂, he₂S⟩ he₂I he₂m))
  obtain ⟨g, hgw, hgm, hgl⟩ := hOne
  have hgt := leafEdge_eq_of_legEdge κ hconn hClaw g hgm hgl
  have hwnc : w ≠ centreSource κ := fun h ↦ by
    have := nonDanglingValency_centre κ
    rw [← h, hw2] at this
    omega
  have hgℓ : g.1 ≠ (lastEdge κ m).1 := by
    intro h
    obtain ⟨v, hv, hvt⟩ := exists_leaf_of_isLeafEdge hgl
    have hS : g.1 ∈ LeafFibre.leafSurvivors hv := (LeafFibre.mem_leafSurvivors hv).mpr ⟨g.2, hvt⟩
    have hA := LeafFibre.incident_coreVertex_of_mem_leafSurvivors κ.fullDim hv hS
    have hwA : w ≠ LeafFibre.coreVertex κ.fullDim hv := by
      intro hwA
      have hcl : IsLeafVertex κ.target (TripodFrame.centreTarget κ) := by
        rw [← hwc, hwA]
        exact hv
      exact not_isLeafVertex_of_three_le κ.fullDim (centreSource κ) (three_le_centreSource κ) hcl
    have hcI : Incident κ.data g.1 (centreSource κ) := h ▸ lastEdge_incident κ m
    have hAc : LeafFibre.coreVertex κ.fullDim hv ≠ centreSource κ := by
      intro hAc
      have hcl : IsLeafVertex κ.target (centreSource κ).1.1 := by
        rw [← hAc]
        exact hv
      exact not_isLeafVertex_of_three_le κ.fullDim (centreSource κ) (three_le_centreSource κ) hcl
    have h1 := (eq_or_eq_otherEnd κ.data hcI hA).resolve_left hAc
    rcases eq_or_eq_otherEnd κ.data hcI hgw with h2 | h2
    · exact hwnc h2
    · exact hwA (h2.trans h1.symm)
  refine ⟨hgt ▸ hgl, ⟨g.1, g.2, hgw, hgt, hgℓ⟩, ?_⟩
  -- the index form: two unit edges at an unramified vertex of valency two
  have hPair : nonDanglingIncident κ.data w = {e.1, e₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, hew⟩
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨he₂S, he₂I⟩
    · rw [card_nonDanglingIncident, hw2, Finset.card_pair (Ne.symm he₂ne)]
  have hSum := sum_index_nonDanglingIncident κ.fullDim.danglingEdgeNoGlue w
  rw [hPair, Finset.sum_pair (Ne.symm he₂ne), hw2, hr0,
    legEdge_index κ hconn hClaw e hem,
    legEdge_index κ hconn hClaw ⟨e₂, he₂S⟩ he₂m] at hSum
  push_cast at hSum
  omega

open Classical in
/-- The second leaf survivor under the last edge of leg `k` (junk if `ℓ_k` is not over a leaf
edge). -/
noncomputable def secondSurvivor (k : Fin 3) : κ.data.SourceEdge :=
  if h : ∃ y : κ.data.SourceEdge, ¬ IsDangling κ.data y ∧
      y.1.1 = (lastEdge κ k).1.1.1 ∧ y ≠ (lastEdge κ k).1 then h.choose
  else (lastEdge κ k).1

/-- The leg vertex over `φ(c)` at the second leaf survivor. -/
noncomputable def legVertex (k : Fin 3) : κ.data.SourceVertex :=
  endOver κ.data (secondSurvivor κ k) (TripodFrame.centreTarget κ)

/-- On a detour leg the second survivor exists, survives, lies over the leaf edge under `ℓ_k`, and
is the only surviving edge there besides `ℓ_k`. -/
theorem secondSurvivor_spec {k : Fin 3} (hDet : IsLeafEdge κ.target (lastEdge κ k).1.1.1) :
    ¬ IsDangling κ.data (secondSurvivor κ k) ∧
      (secondSurvivor κ k).1.1 = (lastEdge κ k).1.1.1 ∧
      secondSurvivor κ k ≠ (lastEdge κ k).1 ∧
      ∀ y : κ.data.SourceEdge, ¬ IsDangling κ.data y → y.1.1 = (lastEdge κ k).1.1.1 →
        y ≠ (lastEdge κ k).1 → y = secondSurvivor κ k := by
  classical
  obtain ⟨v, hv, hvt⟩ := exists_leaf_of_isLeafEdge hDet
  have hCard := LeafFibre.leafSurvivors_card κ.fullDim hv
  have hℓS : (lastEdge κ k).1 ∈ LeafFibre.leafSurvivors hv :=
    (LeafFibre.mem_leafSurvivors hv).mpr ⟨(lastEdge κ k).2, hvt⟩
  have hEx : ∃ y : κ.data.SourceEdge, ¬ IsDangling κ.data y ∧
      y.1.1 = (lastEdge κ k).1.1.1 ∧ y ≠ (lastEdge κ k).1 := by
    obtain ⟨y, hy, hyne⟩ := Finset.exists_mem_ne (by omega : 1 < (LeafFibre.leafSurvivors
      (data := κ.data) hv).card) (lastEdge κ k).1
    obtain ⟨hyS, hyt⟩ := (LeafFibre.mem_leafSurvivors hv).mp hy
    exact ⟨y, hyS, hyt.trans hvt.symm, hyne⟩
  have hDef : secondSurvivor κ k = hEx.choose := dite_eq_left hEx
  obtain ⟨h1, h2, h3⟩ := hEx.choose_spec
  rw [hDef]
  refine ⟨h1, h2, h3, fun y hyS hyt hyne ↦ ?_⟩
  -- the leaf survivors are `ℓ_k` and one other
  have hmem : ∀ z : κ.data.SourceEdge, ¬ IsDangling κ.data z → z.1.1 = (lastEdge κ k).1.1.1 →
      z ∈ LeafFibre.leafSurvivors hv := fun z hzS hzt ↦
    (LeafFibre.mem_leafSurvivors hv).mpr ⟨hzS, hzt.trans hvt⟩
  by_contra hne
  have hsub : ({(lastEdge κ k).1, y, hEx.choose} : Finset κ.data.SourceEdge) ⊆
      LeafFibre.leafSurvivors hv := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hℓS
    · exact hmem _ hyS hyt
    · exact hmem _ h1 h2
  have hle := Finset.card_le_card hsub
  rw [hCard, Finset.card_insert_of_notMem (by simp [Ne.symm hyne, Ne.symm h3]),
    Finset.card_pair hne] at hle
  omega

/-- The leg vertex of a detour leg is a tripod vertex of surviving valency two over `φ(c)`, on leg
`k`. -/
theorem legVertex_spec (hClaw : TripodFrame.IsClaw κ) {k : Fin 3}
    (hDet : IsLeafEdge κ.target (lastEdge κ k).1.1.1) :
    nonDanglingValency κ.data (legVertex κ k) = 2 ∧
      (legVertex κ k).1.1 = TripodFrame.centreTarget κ ∧
      ∃ hS : ¬ IsDangling κ.data (secondSurvivor κ k),
        Incident κ.data (secondSurvivor κ k) (legVertex κ k) ∧
        κ.ident.row (NonDanglingEdge.stablePath ⟨secondSurvivor κ k, hS⟩) = legSlot p k := by
  obtain ⟨hS, ht, hne, -⟩ := secondSurvivor_spec κ hDet
  obtain ⟨v, hv, hvt⟩ := exists_leaf_of_isLeafEdge hDet
  have hmemS : secondSurvivor κ k ∈ LeafFibre.leafSurvivors hv :=
    (LeafFibre.mem_leafSurvivors hv).mpr ⟨hS, ht.trans hvt⟩
  have hℓS : (lastEdge κ k).1 ∈ LeafFibre.leafSurvivors hv :=
    (LeafFibre.mem_leafSurvivors hv).mpr ⟨(lastEdge κ k).2, hvt⟩
  have hInc : Incident κ.data (secondSurvivor κ k) (legVertex κ k) :=
    endOver_incident κ.data _ _
  have hOver : (legVertex κ k).1.1 = TripodFrame.centreTarget κ := by
    refine endOver_target κ.data ?_
    rw [ht]
    exact lastEdge_mem_centre κ k
  -- on leg `k`: both survivors lie on the stable path through the leaf fold
  have hRow : κ.ident.row (NonDanglingEdge.stablePath ⟨secondSurvivor κ k, hS⟩) = legSlot p k := by
    rw [LeafFibre.stablePath_eq_of_mem_leafSurvivors κ.fullDim hv hmemS hS,
      ← LeafFibre.stablePath_eq_of_mem_leafSurvivors κ.fullDim hv hℓS (lastEdge κ k).2]
    exact lastEdge_row κ k
  refine ⟨?_, hOver, hS, hInc, hRow⟩
  have hpos : 0 < nonDanglingValency κ.data (legVertex κ k) := by
    rw [← card_nonDanglingIncident]
    exact Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr ⟨hS, hInc⟩⟩
  rcases κ.fullDim.nonDanglingValency_trichotomy (legVertex κ k) with h | h | h
  · omega
  · exact h
  · exfalso
    have hc := eq_centre_of_branch κ hClaw h.ge hOver
    have hcI : Incident κ.data (secondSurvivor κ k) (centreSource κ) := hc ▸ hInc
    exact hne (congrArg Subtype.val (lastEdge_unique κ k (g := ⟨_, hS⟩) hcI hRow))

open Classical in
/-- **The tripod over `φ(c)`**: the surviving tripod vertices over `φ(c)` are the centre and the
two leg vertices of the detour legs, each a single sheet, so their indices add up to three. -/
theorem sum_yCore_direct (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ) :
    (∑ w ∈ (Finset.univ : Finset κ.data.SourceVertex).filter
        (fun w ↦ 0 < nonDanglingValency κ.data w ∧ YCore κ w),
      (if w.1.1 = TripodFrame.centreTarget κ then
        ((κ.data.vertexPartition w.1.1).blockCard w.1.2 : ℤ) else 0)) = 3 := by
  classical
  set D := (Finset.univ : Finset (Fin 3)).filter fun m ↦ IsLeafEdge κ.target (lastEdge κ m).1.1.1
  have hDcard : D.card = 2 := by
    obtain ⟨k0, hk0, hU⟩ := existsUnique_not_leaf κ hconn hClaw
    have hD : D = (Finset.univ : Finset (Fin 3)).erase k0 := by
      ext m
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · intro hm hmk
        rw [hmk] at hm
        exact hk0 hm
      · intro hmk
        by_contra hm
        exact hmk (hU m hm)
    rw [hD, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  set Sc := (Finset.univ : Finset κ.data.SourceVertex).filter
    (fun w ↦ (0 < nonDanglingValency κ.data w ∧ YCore κ w) ∧
      w.1.1 = TripodFrame.centreTarget κ)
  have hSc : Sc = insert (centreSource κ) (D.image (legVertex κ)) := by
    ext w
    simp only [Sc, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨hw0, hY⟩, hwc⟩
      rcases hY with hY | ⟨hw2, e, hew, heG⟩
      · exact Or.inl hY
      · right
        rcases isGSlot_or_eq_legSlot (κ.ident.row e.stablePath) with hG | ⟨m, hm⟩
        · exact absurd hG heG
        obtain ⟨hDet, ⟨y, hyS, hyw, hyt, hyne⟩, -⟩ :=
          legVertex_centre κ hconn hClaw hw2 hwc e hew hm
        refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDet⟩, ?_⟩
        have hy := (secondSurvivor_spec κ hDet).2.2.2 y hyS hyt hyne
        unfold legVertex
        rw [← hy]
        exact endOver_eq_of_incident κ.data hyw hwc
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · refine ⟨⟨by have := three_le_centreSource κ; omega, Or.inl rfl⟩, rfl⟩
      · have hDet := (Finset.mem_filter.mp hm).2
        obtain ⟨hv2, hvc, hS, hInc, hRow⟩ := legVertex_spec κ hClaw hDet
        refine ⟨⟨by omega, Or.inr ⟨hv2, ⟨_, hS⟩, hInc, ?_⟩⟩, hvc⟩
        rw [hRow]
        exact legSlot_not_isGSlot m
  have hcNot : centreSource κ ∉ D.image (legVertex κ) := by
    intro h
    obtain ⟨m, hm, hmc⟩ := Finset.mem_image.mp h
    have := (legVertex_spec κ hClaw (Finset.mem_filter.mp hm).2).1
    rw [hmc, nonDanglingValency_centre] at this
    omega
  have hInj : Set.InjOn (legVertex κ) D := by
    intro m hm m' hm' hmm
    obtain ⟨hv2, -, hS, hInc, hRow⟩ := legVertex_spec κ hClaw (Finset.mem_filter.mp hm).2
    obtain ⟨-, -, hS', hInc', hRow'⟩ :=
      legVertex_spec κ hClaw (Finset.mem_filter.mp hm').2
    rw [← hmm] at hInc'
    by_cases hEq : secondSurvivor κ m = secondSurvivor κ m'
    · have hrr : κ.ident.row (NonDanglingEdge.stablePath ⟨secondSurvivor κ m, hS⟩) =
          legSlot p m' := by
        rw [show (⟨secondSurvivor κ m, hS⟩ : NonDanglingEdge κ.data) =
          ⟨secondSurvivor κ m', hS'⟩ from Subtype.ext hEq]
        exact hRow'
      exact legSlot_injective (hRow.symm.trans hrr)
    · have hCons : Consecutive κ.data ⟨secondSurvivor κ m, hS⟩ ⟨secondSurvivor κ m', hS'⟩ :=
        ⟨fun h ↦ hEq (congrArg Subtype.val h), _, hInc, hInc', hv2⟩
      have := stablePath_eq_of_consecutive hCons
      rw [this] at hRow
      exact legSlot_injective (hRow.symm.trans hRow')
  have hcard : Sc.card = 3 := by
    rw [hSc, Finset.card_insert_of_notMem hcNot, Finset.card_image_of_injOn hInj, hDcard]
  have hOneIdx : ∀ w ∈ Sc, ((κ.data.vertexPartition w.1.1).blockCard w.1.2 : ℤ) = 1 := by
    intro w hw
    rw [hSc] at hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact_mod_cast blockCard_centre κ hconn hClaw
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hv2, hvc, hS, hInc, hRow⟩ :=
        legVertex_spec κ hClaw (Finset.mem_filter.mp hm).2
      exact_mod_cast (legVertex_centre κ hconn hClaw hv2 hvc ⟨_, hS⟩ hInc hRow).2.2
  rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_congr rfl hOneIdx]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast hcard

/-! ### The dangling branches at the tripod -/

/-- A leg edge with an end at a vertex `u` that is neither a leaf nor `φ(c)` is not a leaf edge: a
leaf edge under a leg lies at `φ(c)` (`leafEdge_eq_of_legEdge`), and its ends `u` and `φ(c)` would
then include a leaf. -/
theorem legEdge_not_leaf_at (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    {m : Fin 3} (g : NonDanglingEdge κ.data) (hgm : κ.ident.row g.stablePath = legSlot p m)
    {u : κ.target.V} (hgu : (g.1.1.1 : κ.target.V × κ.target.V).1 = u ∨
      (g.1.1.1 : κ.target.V × κ.target.V).2 = u)
    (huc : u ≠ TripodFrame.centreTarget κ) (hul : ¬ IsLeafVertex κ.target u) :
    ¬ IsLeafEdge κ.target g.1.1.1 := by
  intro hLeaf
  have ht := leafEdge_eq_of_legEdge κ hconn hClaw g hgm hLeaf
  have hc : (g.1.1.1 : κ.target.V × κ.target.V).1 = TripodFrame.centreTarget κ ∨
      (g.1.1.1 : κ.target.V × κ.target.V).2 = TripodFrame.centreTarget κ := by
    rw [ht]
    exact (Finset.mem_filter.mp (lastEdge_mem_centre κ m)).2
  have hcl := vertex_degree_ne_one_of_three_le κ.fullDim (centreSource κ) (three_le_centreSource κ)
  have hul' : vertex_degree κ.target u ≠ 1 := fun h ↦ hul (isLeafVertex_of_vertex_degree h)
  unfold IsLeafEdge at hLeaf
  rcases hc with h1 | h1 <;> rcases hgu with h2 | h2
  · exact huc (h2.symm.trans h1)
  · rcases hLeaf with h3 | h3
    · rw [h1] at h3
      exact hcl h3
    · rw [h2] at h3
      exact hul' h3
  · rcases hLeaf with h3 | h3
    · rw [h2] at h3
      exact hul' h3
    · rw [h1] at h3
      exact hcl h3
  · exact huc (h2.symm.trans h1)

/-- **The dangling branches at the tripod avoid `φ(c)`** (Corollary 4.10: the dangling trees on the
tripod side do not reach `φ(c)`).

At a vertex over `φ(c)` a walk to `φ(c)` avoiding it is impossible. The centre lies over `φ(c)`,
and the leaf folds carry no dangling edge. At a leg vertex `w` over `u ≠ φ(c)`, off the leaves,
`|w| = 1` (`legEdge_index`), so a dangling edge at `w` lies over an edge `t` at `u` other than the
targets `g, g₂` of the two leg edges at `w`. Suppose `φ(c)` is reachable from the far end of `t`
avoiding `u`; then `φ(c)` is across the cut at `t` from `u` (`below_iff_of_reachP`), so on `u`'s
side of the cuts at `g` and at `g₂` (`not_beyond_both`). But the leg crosses each of those cuts
exactly once (pass-once, `legEdge_eq_of_target_eq`), so the mark image is across both from `u`
(`markSource_iff_not_centreSource`), which `not_beyond_both` forbids. -/
theorem branch_avoids_centre (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    {w : κ.data.SourceVertex} (hw : 0 < nonDanglingValency κ.data w) (hY : YCore κ w)
    (e : PendantRetraction.AttachedEdge w) :
    ¬ DanglingSideStructure.ReachP κ.target (fun x ↦ x ≠ w.1.1)
      (DanglingSideStructure.chosenDangling e.2.2).inner.1.1 (TripodFrame.centreTarget κ) := by
  classical
  set item := DanglingSideStructure.chosenDangling e.2.2 with hitem
  have hOuter : item.outer = w := PendantRetraction.outer_eq_of_incident hw item e.2.1
  have hInnerInc : Incident κ.data e.1 item.inner := by
    rcases item.ends with h | h
    · rw [Incident, h]
      exact Or.inl rfl
    · rw [Incident, h]
      exact Or.inr rfl
  have hyu : item.inner.1.1 ≠ w.1.1 := by
    have hT := TargetGeodesic.Dart.coe_fst_ne_snd e.1.1.1
    have hE1 : ((κ.data.sourceEnds e.1).1).1.1 = (e.1.1.1 : κ.target.V × κ.target.V).1 := rfl
    have hE2 : ((κ.data.sourceEnds e.1).2).1.1 = (e.1.1.1 : κ.target.V × κ.target.V).2 := rfl
    intro hEq
    rcases item.ends with h | h
    · rw [h] at hE1 hE2
      change item.inner.1.1 = _ at hE1
      change item.outer.1.1 = _ at hE2
      rw [hOuter] at hE2
      exact hT (hE1.symm.trans (hEq.trans hE2))
    · rw [h] at hE1 hE2
      change item.outer.1.1 = _ at hE1
      change item.inner.1.1 = _ at hE2
      rw [hOuter] at hE1
      exact hT (hE1.symm.trans (hEq.symm.trans hE2))
  have htu := incident_target e.2.1
  have hty := incident_target hInnerInc
  intro hReach
  by_cases hwc : w.1.1 = TripodFrame.centreTarget κ
  · rcases Relation.ReflTransGen.cases_tail hReach with h | ⟨b, -, -, hb⟩
    · exact hyu (h.symm.trans hwc.symm)
    · exact hb hwc.symm
  rcases hY with hc | ⟨hw2, g, hgw, hgG⟩
  · exact hwc (by rw [hc]; rfl)
  rcases isGSlot_or_eq_legSlot (κ.ident.row g.stablePath) with hG | ⟨m, hm⟩
  · exact hgG hG
  by_cases hLeafU : IsLeafVertex κ.target w.1.1
  · -- the leaf fold carries no dangling edge
    have hwA : w = LeafFibre.coreVertex κ.fullDim hLeafU := by
      by_contra hne'
      have hblock : (⟨w.1.2, w.2⟩ : (κ.data.vertexPartition w.1.1).Blocks) ≠
          LeafFibre.coreBlock κ.fullDim hLeafU := by
        intro h
        apply hne'
        show w = StableLocalProperties.blockVertex κ.data w.1.1 (LeafFibre.coreBlock κ.fullDim hLeafU)
        rw [← h]
        rfl
      have h0 := LeafFibre.nonDanglingValency_other κ.fullDim hLeafU hblock
      change nonDanglingValency κ.data w = 0 at h0
      omega
    exact LeafFibre.not_isDangling_of_incident_coreVertex κ.fullDim hLeafU (hwA ▸ e.2.1) e.2.2
  -- a leg vertex off the leaves and off `φ(c)`
  have hcard : 2 ≤ (GluingDatum.incidentEdges w.1.1).card := by
    have hgu := ((incident_iff_target_mem_and_rel κ.data g.1 w).mp hgw).1
    have h0 : 0 < (GluingDatum.incidentEdges w.1.1).card := Finset.card_pos.mpr ⟨_, hgu⟩
    have h1 : (GluingDatum.incidentEdges w.1.1).card ≠ 1 := hLeafU
    omega
  have hr1 := DivalentSourceLocal.localRamification_le_one_of_nonleaf κ.data κ.fullDim.valid w
    (κ.fullDim.changeMinimal _) hcard
  have hr0 := κ.data.localRamification_nonneg w.1.1 (κ.fullDim.valid.2 _) ⟨w.1.2, w.2⟩
  set g₂ := stepEdge κ.data hw2 g.1 with hg₂
  have hg₂S := stepEdge_not_dangling κ.data hw2 g.1
  have hg₂I := stepEdge_incident κ.data hw2 g.1
  have hg₂ne := stepEdge_ne κ.data hw2 g.1
  have hCons : Consecutive κ.data g ⟨g₂, hg₂S⟩ :=
    ⟨fun h ↦ hg₂ne (congrArg Subtype.val h).symm, w, hgw, hg₂I, hw2⟩
  have hg₂m : κ.ident.row (NonDanglingEdge.stablePath ⟨g₂, hg₂S⟩) = legSlot p m := by
    rw [← stablePath_eq_of_consecutive hCons]
    exact hm
  have hT12 := RowWalk.target_ne_of_localRamification_le_one κ.fullDim.danglingEdgeNoGlue hw2
    hr1 g.2 hgw hg₂S hg₂I (Ne.symm hg₂ne)
  -- `|w| = 1`
  have hPair : nonDanglingIncident κ.data w = {g.1, g₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨g.2, hgw⟩
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨hg₂S, hg₂I⟩
    · rw [card_nonDanglingIncident, hw2, Finset.card_pair (Ne.symm hg₂ne)]
  have hSum := sum_index_nonDanglingIncident κ.fullDim.danglingEdgeNoGlue w
  have hgi := legEdge_index κ hconn hClaw g hm
  have hg₂i := legEdge_index κ hconn hClaw ⟨g₂, hg₂S⟩ hg₂m
  rw [hPair, Finset.sum_pair (Ne.symm hg₂ne), hw2, hgi] at hSum
  change (1 : ℤ) + (κ.data.sourceEdgeIndex g₂ : ℤ) = _ at hSum
  rw [show κ.data.sourceEdgeIndex g₂ = 1 from hg₂i] at hSum
  have hw1 : (κ.data.vertexPartition w.1.1).blockCard w.1.2 = 1 := by
    push_cast at hSum
    omega
  -- the dangling edge lies over neither leg direction
  have hOff : ∀ dir : κ.target.edges, (dir = g.1.1.1 ∨ dir = g₂.1.1) → e.1.1.1 ≠ dir := by
    intro dir hdir heq
    have hdirMem : dir ∈ GluingDatum.incidentEdges w.1.1 := by
      rcases hdir with rfl | rfl
      · exact ((incident_iff_target_mem_and_rel κ.data g.1 w).mp hgw).1
      · exact ((incident_iff_target_mem_and_rel κ.data g₂ w).mp hg₂I).1
    have hcardD := PendantFibre.danglingDirection_card_of_two_survivors
      κ.fullDim.danglingEdgeNoGlue w hw2 ⟨g.1, hgw⟩ ⟨g₂, hg₂I⟩ g.2 hg₂S (Ne.symm hg₂ne) dir
      hdirMem
    let x : IncidentSourceEdge κ.data w := ⟨e.1, e.2.1⟩
    have hmemD : x ∈ PendantFibre.danglingDirection w dir :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, heq, e.2.2⟩
    have hpos : 0 < (PendantFibre.danglingDirection w dir).card :=
      Finset.card_pos.mpr ⟨_, hmemD⟩
    rw [hw1] at hcardD
    change _ = _ - (if g.1.1.1 = dir then (κ.data.sourceEdgeIndex g.1 : ℤ) else 0) -
      (if g₂.1.1 = dir then (κ.data.sourceEdgeIndex g₂ : ℤ) else 0) at hcardD
    rw [hgi, show κ.data.sourceEdgeIndex g₂ = 1 from hg₂i] at hcardD
    rcases hdir with rfl | rfl
    · rw [ite_eq_left rfl, ite_eq_right (Ne.symm hT12)] at hcardD
      omega
    · rw [ite_eq_right hT12, ite_eq_left rfl] at hcardD
      omega
  -- the cuts
  obtain ⟨A⟩ := TargetGeodesic.exists_treeRank κ.target κ.fullDim.targetConnected
    κ.fullDim.targetGenus
  have huc := hwc
  have hgU := incident_target hgw
  have hg₂U := incident_target hg₂I
  -- the leg crosses the cut at each of its edges at `w` once
  have hSide : ∀ gg : NonDanglingEdge κ.data, Incident κ.data gg.1 w →
      κ.ident.row gg.stablePath = legSlot p m →
      (Below A gg.1.1.1 (TripodFrame.markSource κ m).1.1 ↔
        ¬ Below A gg.1.1.1 (TripodFrame.centreTarget κ)) := by
    intro gg hggw hggm
    have hNL := legEdge_not_leaf_at κ hconn hClaw gg hggm (incident_target hggw) huc hLeafU
    refine markSource_iff_not_centreSource κ m (Below A gg.1.1.1) gg hggm
      (fun h ↦ (below_fst_iff_snd A _ _).mp h rfl) ?_
    intro a ha hane
    refine (below_fst_iff_snd A _ _).mpr fun hEq ↦ hane ?_
    exact legEdge_eq_of_target_eq κ hconn hClaw a gg ha hggm hEq (hEq ▸ hNL)
  -- `φ(c)` would be across the cut at `t`
  have hBeyond : ¬ (Below A e.1.1.1 (TripodFrame.centreTarget κ) ↔ Below A e.1.1.1 w.1.1) := by
    have hR := below_iff_of_reachP A htu hyu hReach
    have hE : ¬ (Below A e.1.1.1 (e.1.1.1 : κ.target.V × κ.target.V).1 ↔
        Below A e.1.1.1 (e.1.1.1 : κ.target.V × κ.target.V).2) := fun h ↦
      (below_fst_iff_snd A e.1.1.1 e.1.1.1).mp h rfl
    rw [iff_ends (Q := Below A e.1.1.1) hty htu hyu] at hE
    intro h
    exact hE (hR.trans h)
  -- so on `u`'s side of the cuts at the two leg edges, and the mark across both
  have hNear : ∀ gg : NonDanglingEdge κ.data, Incident κ.data gg.1 w →
      κ.ident.row gg.stablePath = legSlot p m →
      ¬ (Below A gg.1.1.1 (TripodFrame.markSource κ m).1.1 ↔ Below A gg.1.1.1 w.1.1) := by
    intro gg hggw hggm hiff
    have hdir : gg.1.1.1 = g.1.1.1 ∨ gg.1.1.1 = g₂.1.1 := by
      rcases eq_or_eq_stepEdge κ.data hw2 g.2 hgw gg.2 hggw with h | h
      · exact Or.inl (congrArg (fun x : κ.data.SourceEdge ↦ x.1.1) h)
      · exact Or.inr (congrArg (fun x : κ.data.SourceEdge ↦ x.1.1) h)
    have hc : Below A gg.1.1.1 (TripodFrame.centreTarget κ) ↔ Below A gg.1.1.1 w.1.1 := by
      by_contra hc
      exact not_beyond_both A htu (incident_target hggw) (hOff gg.1.1.1 hdir) hBeyond hc
    have hs := hSide gg hggw hggm
    exact iff_not_self ((hiff.trans hc.symm).symm.trans hs)
  exact not_beyond_both A hgU hg₂U hT12 (hNear g hgw hm) (hNear ⟨g₂, hg₂S⟩ hg₂I hg₂m)

/-- **`k₀ = 0`** (Corollary 4.10, case (b)), in the form `δ_Y(φ(c)) = 3`. Group the source vertices
over `φ(c)` that retract onto the tripod by the surviving vertex they retract to (at most one,
`PendantRetraction.surviving_vertex_unique`); each group is a retracted fibre, which the branch
census `PendantRetraction.retractedFibre_eq_branch_sum` evaluates as the direct local degree plus
the branches through `φ(c)`. The branches contribute nothing (`branch_avoids_centre`), and the
direct terms add up to three (`sum_yCore_direct`). -/
theorem sum_yCore_centre (hconn : core.Connected) (hClaw : TripodFrame.IsClaw κ)
    [DecidablePred (OverCentreY κ)] :
    (∑ v : κ.data.SourceVertex,
      if OverCentreY κ v then ((κ.data.vertexPartition v.1.1).blockCard v.1.2 : ℤ) else 0) =
      3 := by
  classical
  set S := (Finset.univ : Finset κ.data.SourceVertex).filter
    (fun w ↦ 0 < nonDanglingValency κ.data w ∧ YCore κ w) with hS
  -- each source vertex retracts onto at most one surviving vertex
  have hPoint : ∀ v : κ.data.SourceVertex,
      (if OverCentreY κ v then ((κ.data.vertexPartition v.1.1).blockCard v.1.2 : ℤ) else 0) =
        ∑ w ∈ S, (if PendantRetraction.retractVertex v = PendantRetraction.retractVertex w ∧
          v.1.1 = TripodFrame.centreTarget κ then
            ((κ.data.vertexPartition v.1.1).blockCard v.1.2 : ℤ) else 0) := by
    intro v
    by_cases hO : OverCentreY κ v
    · rw [ite_eq_left hO]
      obtain ⟨hvc, w₀, hw₀, hY₀, hR₀⟩ := hO
      rw [Finset.sum_eq_single w₀]
      · rw [ite_eq_left ⟨hR₀, hvc⟩]
      · intro w hwS hne
        rw [ite_eq_right]
        rintro ⟨hR, -⟩
        exact hne (PendantRetraction.surviving_vertex_unique (Finset.mem_filter.mp hwS).2.1 hw₀
          (hR.symm.trans hR₀))
      · intro h
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw₀, hY₀⟩) h
    · rw [ite_eq_right hO]
      symm
      refine Finset.sum_eq_zero fun w hwS ↦ ?_
      rw [ite_eq_right]
      rintro ⟨hR, hvc⟩
      exact hO ⟨hvc, w, (Finset.mem_filter.mp hwS).2.1, (Finset.mem_filter.mp hwS).2.2, hR⟩
  rw [Finset.sum_congr rfl fun v _ ↦ hPoint v, Finset.sum_comm]
  -- each group is a retracted fibre
  have hGroup : ∀ w ∈ S, (∑ v : κ.data.SourceVertex,
      (if PendantRetraction.retractVertex v = PendantRetraction.retractVertex w ∧
        v.1.1 = TripodFrame.centreTarget κ then
          ((κ.data.vertexPartition v.1.1).blockCard v.1.2 : ℤ) else 0)) =
      (if w.1.1 = TripodFrame.centreTarget κ then
        ((κ.data.vertexPartition w.1.1).blockCard w.1.2 : ℤ) else 0) := by
    intro w hwS
    obtain ⟨hw0, hY⟩ := (Finset.mem_filter.mp hwS).2
    have hB := PendantRetraction.retractedFibre_eq_branch_sum κ.fullDim
      (TripodFrame.centreTarget κ) hw0
    have hZero : (∑ e : PendantRetraction.AttachedEdge w,
        if DanglingSideStructure.ReachP κ.target (fun x ↦ x ≠ w.1.1)
          (DanglingSideStructure.chosenDangling e.2.2).inner.1.1 (TripodFrame.centreTarget κ)
        then (1 : ℤ) else 0) = 0 :=
      Finset.sum_eq_zero fun e _ ↦ ite_eq_right (branch_avoids_centre κ hconn hClaw hw0 hY e)
    rw [hZero, add_zero] at hB
    rw [← hB]
    unfold PendantRetraction.retractedFibre
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl hGroup]
  convert sum_yCore_direct κ hconn hClaw

end GenusSixExistence.Tripod.ClawShape
