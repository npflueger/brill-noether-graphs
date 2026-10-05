module

public import DraismaVargas.LocalCases.CertifiedPencil
public import Utilities.Subdivision.TrivalentExpansion

@[expose] public section

/-!
# The stable-model reduction, and the constraint that forces it

## 1.  The constraint

Composing the march with its certified terminal payload is **vacuous unless the
requested core is trivalent**.  `dimension_forced` below is that fact, read off
the certified terminal payload alone:

* `InputRefinementData.InputInterface.slot : Fin p ≃ coordinate`;
* `FullDimensionalSourcePresentation.labelling.targetEdge : coordinate ≃ edges`;
* `FullDimensionalSourcePresentation.saturated`;
* `TerminalExhausts.SourceGenusMatches` and `Spec.genus_graph`.

Chaining them gives `p = 2 g + 2 * degree - 5` for the *requested* `spec`, and at
the even-genus degree `⌈g/2⌉ + 1` of the main theorem that is exactly
`2 p = 3 n`, i.e. `n = 2g - 2` and `p = 3g - 3`.  `6 ≤ g` is never used.
`not_carriesCertifiedPencil_of_ne` is the contrapositive: off `2 p = 3 n` no
certified terminal payload exists at all.

Consequently the general statement, quantified over *all* connected specs,
cannot be reached from the march without an **outer** reduction producing a
trivalent representative.  That reduction is the subject of this file.

## 2.  What this file supplies

The reduction has three moves: contract bridges (`SpecBridge`,
`BridgeReduction`), suppress bivalent vertices and reorient at markers
(`StableModelPackaging`, through
`Utilities.Certificate.PseudocorePresentation.exists_reduced`), then expand to
a cubic core.  Pruning dangling trees (`Utilities.Certificate.LeafPruning`) is
not needed, a pendant tree being made of bridges.  The expansion is
`Utilities.Subdivision.TrivalentExpansion.exists_expansion` — **except at
markers**, and that exception is the whole of the new mathematics here.

A reduced loopless core still carries bivalent **markers**: a pair of slots
running to one common partner, which is how a *loop* of the underlying metric
graph is displayed looplessly.  `exists_expansion` demands
`3 ≤ slotValence C w` at every vertex, which a marker fails, and
`TrivalentExpansion.data` never emits a `CoreExpansion.SlotKind.double`.

`exists_markerExpansion` is the marker-aware replacement.  It keeps the
centipede, but (i) indexes the carriers by the slots that are *not* the
returning half of a loop, so a loop is carried by a single `double` slot whose
two endpoints lie in one fibre, and (ii) orders the slot ends at each vertex so
that the two halves of every loop land on **different** centipede vertices —
`posFn` puts the outgoing halves first and the returning halves last, and
`legIndex_lt_legIndex` is the arithmetic that separates them.  The counts are
unchanged, `2 (g-1)` vertices and `3 (g-1)` slots, because a marker contributes
`slotValence - 2 = 0` centipede vertices and its second slot contributes no
carrier; `sum_valence_sub_three` records the bookkeeping.

## 3.  Where it stops, and why that is a theorem

`Stable` carries two hypotheses: every non-marker vertex has valence at least
three (automatic for a reduced leafless core of genus `≠ 1`, via
`partner_not_bivalent_of_genus_ne_one`), and **every marker's partner has
valence at least four**.  The second cannot be dropped, and not for want of a
better construction:

*Let `H` be a loopless cubic core and let `Γ` be obtained from `H` by an
equal-genus topological contraction with connected fibres.  Writing `T_v` for
the fibre over a vertex `v` of `Γ`, the contracted slots inside `T_v` form a
spanning tree of it, so `|T_v| - 1` of them, and the handshake at `T_v` reads
`3 |T_v| = 2 (|T_v| - 1) + deg_Γ(v)`, i.e.* `|T_v| = deg_Γ(v) - 2`.

A loop at `v` is a big slot with both endpoints in `T_v`
(`double_fib_eq`), so it needs `2 ≤ |T_v|`, i.e. `4 ≤ deg_Γ(v)`.  At
`deg_Γ(v) = 3` the fibre is a single vertex and the big slot is a **loop of the
big core**, which `ExpansionData.Conditions` forbids —
`not_conditions_of_singleton_fibre` is that step, machine-checked.  The fibre
identity itself is *not* formalised here; it is the Euler accounting of
`Certificate.GraphContractionCertificate.fibreGraph_edge_card_add_one_eq_vertex_card_of_genus_eq`.

The excluded configuration is a **pendant loop**: a cycle meeting the rest of
the graph at one point, attached by a bridge.  Such graphs exist at every genus
(a chain of one-vertex loops on a tree), they survive leaf pruning and bivalent
suppression, and they are produced by the development's own odd-genus route —
`DraismaVargas.OddGenusTwoCycle.extension spec root` attaches a two-cycle at
`root`, and if `root` has valence one in `spec` the extension has a pendant
loop.  This is why the *bridgeless* hypothesis is needed here; it does not
obstruct the reduction as a whole: `SpecBridge`/`BridgeReduction` contract every
bridge first, and `StableModelPackaging.exists_cubicModel` produces a cubic
model for every connected specification of genus at least two, with no
`Marking` or `Stable` input.

§8 gives a witness on each side: `wedge_expansion` (a core of minimum slot
valence *two* that `exists_expansion` cannot touch and `exists_markerExpansion`
expands to the theta graph) and `dumbbell_not_stable` (a leafless connected core
whose markers sit at three-valent partners).
-/

namespace DraismaVargas.LocalCases

namespace StableModelReduction

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.PseudocorePresentation
open Utilities.Subdivision.CoreExpansion
open Utilities.Subdivision.TrivalentExpansion (legIndex legIndex_lt tailEnd headEnd
  three_le_card_of_three_mem exists_adjacent_flip)
open ExplicitPotential
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.TerminalExhausts
open DraismaVargas.LocalCases.TraversalPresentation

/-! ## 1.  The forcing theorem -/

section Forcing

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]

/-- **The certified payload pins the requested edge count.**  A certified
terminal payload for `spec : Spec n p` at `degree` forces
`p = 2 * genus + 2 * degree - 5`.  Nothing about the genus is assumed. -/
theorem dimension_forced {n p degree : ℕ} {spec : Spec n p}
    {matrix : Matrix coordinate coordinate ℚ} {start finish : coordinate → ℚ}
    (hFinish : ∀ i, 0 ≤ finish i)
    (certified : CertifiedPencil.CarriesCertifiedPencil spec degree matrix start finish) :
    (p : ℤ) = 2 * ((p : ℤ) - (n : ℤ) + 1) + 2 * degree - 5 := by
  obtain ⟨target, data, wall, candidate, fullDim, strong, -, -, -, -, -, -,
    hSource, hCert⟩ := certified
  obtain ⟨iface, -, -, -⟩ := hCert hFinish
  have hCardP : Fintype.card coordinate = p := by
    simpa using (Fintype.card_congr iface.slot).symm
  have hCardE : Fintype.card coordinate =
      Fintype.card (TargetExpansion.graph target wall candidate.right).edges :=
    Fintype.card_congr fullDim.labelling.targetEdge
  have hSat := fullDim.saturated
  have hGenusEq : genus candidate.datum.sourceGraph = (p : ℤ) - (n : ℤ) + 1 := by
    have hEq := hSource
    rw [TerminalExhausts.SourceGenusMatches] at hEq
    rw [hEq, Spec.genus_graph]
  rw [hGenusEq] at hSat
  have hEdges : ((TargetExpansion.graph target wall candidate.right).edges.card : ℤ)
      = (p : ℤ) := by
    have hcard : Fintype.card (TargetExpansion.graph target wall candidate.right).edges
        = p := by
      rw [← hCardE, hCardP]
    simp only [← hcard]; norm_cast; simp
  rw [hEdges] at hSat
  exact hSat

/-- **At the even-genus degree of the main theorem the requested core must be
trivalent.** `6 ≤ g` is not needed; only `n ≤ p + 1` and evenness of the
genus. -/
theorem two_mul_p_eq_three_mul_n {n p : ℕ} {spec : Spec n p}
    {matrix : Matrix coordinate coordinate ℚ} {start finish : coordinate → ℚ}
    (hLe : n ≤ p + 1) (hEven : Even (p + 1 - n)) (hFinish : ∀ i, 0 ≤ finish i)
    (certified : CertifiedPencil.CarriesCertifiedPencil spec ((p + 2 - n) / 2 + 1)
      matrix start finish) :
    2 * p = 3 * n := by
  have h := dimension_forced hFinish certified
  obtain ⟨k, hk⟩ := hEven
  have hd : (p + 2 - n) / 2 + 1 = k + 1 := by omega
  rw [hd] at h
  push_cast at h
  omega

/-- **The contrapositive: off `2 p = 3 n` there is no certified payload.**  So a
certified terminal payload cannot serve a non-trivalent request directly,
whatever the march does. -/
theorem not_carriesCertifiedPencil_of_ne {n p : ℕ} {spec : Spec n p}
    {matrix : Matrix coordinate coordinate ℚ} {start finish : coordinate → ℚ}
    (hLe : n ≤ p + 1) (hEven : Even (p + 1 - n)) (hFinish : ∀ i, 0 ≤ finish i)
    (hNe : 2 * p ≠ 3 * n) :
    ¬ CertifiedPencil.CarriesCertifiedPencil spec ((p + 2 - n) / 2 + 1)
      matrix start finish :=
  fun certified ↦ hNe (two_mul_p_eq_three_mul_n hLe hEven hFinish certified)

end Forcing

/-! ## 2.  Ordering the slot ends at a core vertex -/

variable {n p : ℕ}

def key (x : Fin p × Bool) : ℕ := 2 * x.1.val + (if x.2 then 1 else 0)

theorem key_injective : Function.Injective (key (p := p)) := by
  rintro ⟨j, s⟩ ⟨j', s'⟩ h
  have h' : 2 * j.val + (if s then 1 else 0) = 2 * j'.val + (if s' then 1 else 0) := h
  clear h
  cases s <;> cases s' <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] at h'
  · have hjj : j = j' := Fin.ext (by omega)
    rw [hjj]
  · omega
  · omega
  · have hjj : j = j' := Fin.ext (by omega)
    rw [hjj]

def rank (T : Finset (Fin p × Bool)) (x : Fin p × Bool) : ℕ :=
  (T.filter fun y => key y < key x).card

theorem rank_lt_card {T : Finset (Fin p × Bool)} {x : Fin p × Bool} (hx : x ∈ T) :
    rank T x < T.card :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
    ⟨x, hx, by simp⟩)

theorem rank_lt_rank {T : Finset (Fin p × Bool)} {x y : Fin p × Bool}
    (hx : x ∈ T) (h : key x < key y) : rank T x < rank T y := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ?_)
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_trans hz.2 h⟩
  · exact ⟨x, by simp [Finset.mem_filter, hx, h], by simp⟩

theorem rank_inj {T : Finset (Fin p × Bool)} {x y : Fin p × Bool}
    (hx : x ∈ T) (hy : y ∈ T) (h : rank T x = rank T y) : x = y := by
  by_contra hne
  have hkey : key x ≠ key y := fun hk => hne (key_injective hk)
  rcases Nat.lt_or_ge (key x) (key y) with hlt | hge
  · have := rank_lt_rank hx hlt; omega
  · have hlt : key y < key x := by omega
    have := rank_lt_rank hy hlt; omega

/-! ## Markings -/

/-- A **marking** of a loopless core: an enumeration of its bivalent markers,
each presented as an ordered pair of slots. -/
structure Marking (C : Core n p) where
  first : Fin p → Bool
  second : Fin p → Bool
  mate : Fin p → Fin p
  second_of_first : ∀ j, first j = true → second (mate j) = true
  first_of_second : ∀ j, second j = true → first (mate j) = true
  mate_mate_first : ∀ j, first j = true → mate (mate j) = j
  mate_mate_second : ∀ j, second j = true → mate (mate j) = j
  second_eq_false : ∀ j, first j = true → second j = false
  tail_mate : ∀ j, first j = true → C.tail (mate j) = C.head j
  head_mate : ∀ j, first j = true → C.head (mate j) = C.tail j
  head_unique : ∀ j, first j = true → ∀ j', C.head j' = C.head j → j' = j
  tail_unique : ∀ j, first j = true → ∀ j', C.tail j' = C.head j → j' = mate j

namespace Marking

variable {C : Core n p} (mk : Marking C)

theorem first_eq_false (j : Fin p) (h : mk.second j = true) : mk.first j = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rw [mk.second_eq_false j hc] at h
  exact Bool.noConfusion h

/-- The bivalent vertices named by the marking. -/
def IsMarker (w : Fin n) : Prop := ∃ j : Fin p, mk.first j = true ∧ C.head j = w

instance (w : Fin n) : Decidable (mk.IsMarker w) := by
  unfold IsMarker; infer_instance

theorem slotEnds_marker {j : Fin p} (hj : mk.first j = true) :
    slotEnds C (C.head j) = {(j, true), (mk.mate j, false)} := by
  ext x
  simp only [mem_slotEnds, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    obtain ⟨j', s⟩ := x
    cases s with
    | false =>
        simp only [Bool.false_eq_true, ite_false] at hx
        exact Or.inr (by rw [mk.tail_unique j hj j' hx])
    | true =>
        simp only [ite_true] at hx
        exact Or.inl (by rw [mk.head_unique j hj j' hx])
  · rintro (rfl | rfl)
    · simp
    · simpa using mk.tail_mate j hj

theorem slotValence_marker {j : Fin p} (hj : mk.first j = true) :
    slotValence C (C.head j) = 2 := by
  rw [slotValence, mk.slotEnds_marker hj]
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

theorem not_isMarker_tail {j : Fin p} (hj : mk.second j = false) :
    ¬ mk.IsMarker (C.tail j) := by
  rintro ⟨j₀, hj₀, hEq⟩
  have hjm : j = mk.mate j₀ := mk.tail_unique j₀ hj₀ j hEq.symm
  rw [hjm, mk.second_of_first j₀ hj₀] at hj
  exact Bool.noConfusion hj

theorem not_isMarker_head {j : Fin p} (hj : mk.first j = false) :
    ¬ mk.IsMarker (C.head j) := by
  rintro ⟨j₀, hj₀, hEq⟩
  have hjm : j = j₀ := mk.head_unique j₀ hj₀ j hEq.symm
  rw [hjm, hj₀] at hj
  exact Bool.noConfusion hj

end Marking



/-! ## The three classes of slot ends at a vertex -/

section Classes

variable {C : Core n p} (mk : Marking C) (w : Fin n)

/-- Slot ends at `w` that are the outgoing half of a loop at `w`. -/
def aEnds : Finset (Fin p × Bool) :=
  (slotEnds C w).filter fun x => x.2 = false ∧ mk.first x.1 = true

/-- Slot ends at `w` that are the returning half of a loop at `w`. -/
def bEnds : Finset (Fin p × Bool) :=
  (slotEnds C w).filter fun x => x.2 = true ∧ mk.second x.1 = true

/-- Slot ends at `w` belonging to no loop at `w`. -/
def sEnds : Finset (Fin p × Bool) :=
  (slotEnds C w).filter fun x =>
    ¬ (x.2 = false ∧ mk.first x.1 = true) ∧ ¬ (x.2 = true ∧ mk.second x.1 = true)

/-- The number of loops at `w`. -/
def loopCount : ℕ := (aEnds mk w).card

theorem mem_aEnds {x : Fin p × Bool} :
    x ∈ aEnds mk w ↔ C.tail x.1 = w ∧ x.2 = false ∧ mk.first x.1 = true := by
  simp only [aEnds, Finset.mem_filter, mem_slotEnds]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [h2] at h1
    simp only [Bool.false_eq_true, ite_false] at h1
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, h3⟩
    rw [h2]
    simpa using h1

theorem mem_bEnds {x : Fin p × Bool} :
    x ∈ bEnds mk w ↔ C.head x.1 = w ∧ x.2 = true ∧ mk.second x.1 = true := by
  simp only [bEnds, Finset.mem_filter, mem_slotEnds]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [h2] at h1
    simp only [ite_true] at h1
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, h3⟩
    rw [h2]
    simpa using h1

theorem bEnds_eq_image :
    bEnds mk w = (aEnds mk w).image fun x => (mk.mate x.1, true) := by
  ext y
  simp only [Finset.mem_image]
  constructor
  · intro hy
    rw [mem_bEnds] at hy
    obtain ⟨hhead, hsnd, hsec⟩ := hy
    refine ⟨(mk.mate y.1, false), ?_, ?_⟩
    · rw [mem_aEnds]
      refine ⟨?_, rfl, mk.first_of_second _ hsec⟩
      have h := mk.head_mate _ (mk.first_of_second _ hsec)
      rw [mk.mate_mate_second _ hsec] at h
      rw [← h, hhead]
    · simp only
      rw [mk.mate_mate_second _ hsec]
      exact Prod.ext rfl hsnd.symm
  · rintro ⟨x, hx, rfl⟩
    rw [mem_aEnds] at hx
    obtain ⟨htail, hsnd, hfst⟩ := hx
    rw [mem_bEnds]
    exact ⟨by simpa [mk.head_mate _ hfst] using htail, rfl,
      mk.second_of_first _ hfst⟩

theorem card_bEnds : (bEnds mk w).card = loopCount mk w := by
  rw [bEnds_eq_image, loopCount]
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy hxy
  simp only [Finset.mem_coe] at hx hy
  rw [mem_aEnds] at hx hy
  have hm : mk.mate x.1 = mk.mate y.1 := congrArg Prod.fst hxy
  have h1 : x.1 = y.1 := by
    rw [← mk.mate_mate_first _ hx.2.2, hm, mk.mate_mate_first _ hy.2.2]
  exact Prod.ext h1 (hx.2.1.trans hy.2.1.symm)

theorem mem_classes {x : Fin p × Bool} (hx : x ∈ slotEnds C w) :
    x ∈ aEnds mk w ∨ x ∈ bEnds mk w ∨ x ∈ sEnds mk w := by
  by_cases h1 : x.2 = false ∧ mk.first x.1 = true
  · exact Or.inl (Finset.mem_filter.mpr ⟨hx, h1⟩)
  · by_cases h2 : x.2 = true ∧ mk.second x.1 = true
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hx, h2⟩))
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hx, h1, h2⟩))

theorem card_split :
    loopCount mk w + loopCount mk w + (sEnds mk w).card = slotValence C w := by
  classical
  have hunion : aEnds mk w ∪ bEnds mk w ∪ sEnds mk w = slotEnds C w := by
    ext x
    simp only [Finset.mem_union, aEnds, bEnds, sEnds, Finset.mem_filter]
    tauto
  have hab : Disjoint (aEnds mk w) (bEnds mk w) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [aEnds, bEnds, Finset.mem_filter] at hx hy
    rw [hx.2.1] at hy
    exact Bool.noConfusion hy.2.1
  have habs : Disjoint (aEnds mk w ∪ bEnds mk w) (sEnds mk w) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_union, aEnds, bEnds, sEnds, Finset.mem_filter] at hx hy
    rcases hx with hx | hx
    · exact hy.2.1 hx.2
    · exact hy.2.2 hx.2
  have h1 := Finset.card_union_of_disjoint habs
  have h2 := Finset.card_union_of_disjoint hab
  rw [hunion] at h1
  rw [h2, card_bEnds] at h1
  rw [slotValence]
  simp only [loopCount] at h1 ⊢
  omega

end Classes

/-! ## The order that separates the two halves of every loop -/

section Position

variable {C : Core n p} (mk : Marking C) (w : Fin n)

/-- Position of a slot end at `w`: outgoing loop halves first, returning loop
halves last, everything else in between. -/
def posFn (x : Fin p × Bool) : ℕ :=
  if x.2 = false ∧ mk.first x.1 = true then rank (aEnds mk w) x
  else if x.2 = true ∧ mk.second x.1 = true then
    (slotValence C w - loopCount mk w) + rank (bEnds mk w) x
  else loopCount mk w + rank (sEnds mk w) x

theorem posFn_of_a {x : Fin p × Bool} (hx : x ∈ aEnds mk w) :
    posFn mk w x = rank (aEnds mk w) x := by
  have h := (Finset.mem_filter.mp hx).2
  simp only [posFn, ite_eq_left h]

theorem posFn_of_b {x : Fin p × Bool} (hx : x ∈ bEnds mk w) :
    posFn mk w x = (slotValence C w - loopCount mk w) + rank (bEnds mk w) x := by
  have h := (Finset.mem_filter.mp hx).2
  have hnot : ¬ (x.2 = false ∧ mk.first x.1 = true) := by
    rintro ⟨h1, -⟩
    rw [h1] at h
    exact Bool.noConfusion h.1
  simp only [posFn, ite_eq_right hnot, ite_eq_left h]

theorem posFn_of_s {x : Fin p × Bool} (hx : x ∈ sEnds mk w) :
    posFn mk w x = loopCount mk w + rank (sEnds mk w) x := by
  have h := (Finset.mem_filter.mp hx).2
  simp only [posFn, ite_eq_right h.1, ite_eq_right h.2]

theorem posFn_lt_a {x : Fin p × Bool} (hx : x ∈ aEnds mk w) :
    posFn mk w x < loopCount mk w := by
  rw [posFn_of_a mk w hx]; exact rank_lt_card hx

theorem posFn_ge_b {x : Fin p × Bool} (hx : x ∈ bEnds mk w) :
    slotValence C w - loopCount mk w ≤ posFn mk w x := by
  rw [posFn_of_b mk w hx]; omega

theorem posFn_lt_b {x : Fin p × Bool} (hx : x ∈ bEnds mk w) :
    posFn mk w x < slotValence C w := by
  rw [posFn_of_b mk w hx]
  have h1 := rank_lt_card hx
  rw [card_bEnds] at h1
  have h2 := card_split mk w
  omega

theorem posFn_ge_s {x : Fin p × Bool} (hx : x ∈ sEnds mk w) :
    loopCount mk w ≤ posFn mk w x := by
  rw [posFn_of_s mk w hx]; omega

theorem posFn_lt_s {x : Fin p × Bool} (hx : x ∈ sEnds mk w) :
    posFn mk w x < slotValence C w - loopCount mk w := by
  rw [posFn_of_s mk w hx]
  have h1 := rank_lt_card hx
  have h2 := card_split mk w
  omega

theorem posFn_lt {x : Fin p × Bool} (hx : x ∈ slotEnds C w) :
    posFn mk w x < slotValence C w := by
  have h2 := card_split mk w
  rcases mem_classes mk w hx with h | h | h
  · have := posFn_lt_a mk w h; omega
  · exact posFn_lt_b mk w h
  · have := posFn_lt_s mk w h; omega

theorem posFn_inj {x y : Fin p × Bool} (hx : x ∈ slotEnds C w) (hy : y ∈ slotEnds C w)
    (h : posFn mk w x = posFn mk w y) : x = y := by
  have hsplit := card_split mk w
  rcases mem_classes mk w hx with hax | hbx | hsx <;>
    rcases mem_classes mk w hy with hay | hby | hsy
  · exact rank_inj hax hay (by
      rw [← posFn_of_a mk w hax, ← posFn_of_a mk w hay]; exact h)
  · exact absurd h (by
      have := posFn_lt_a mk w hax; have := posFn_ge_b mk w hby; omega)
  · exact absurd h (by
      have := posFn_lt_a mk w hax; have := posFn_ge_s mk w hsy; omega)
  · exact absurd h (by
      have := posFn_lt_a mk w hay; have := posFn_ge_b mk w hbx; omega)
  · refine rank_inj hbx hby ?_
    have e1 := posFn_of_b mk w hbx
    have e2 := posFn_of_b mk w hby
    omega
  · exact absurd h (by
      have := posFn_ge_b mk w hbx; have := posFn_lt_s mk w hsy; omega)
  · exact absurd h (by
      have := posFn_lt_a mk w hay; have := posFn_ge_s mk w hsx; omega)
  · exact absurd h (by
      have := posFn_ge_b mk w hby; have := posFn_lt_s mk w hsx; omega)
  · refine rank_inj hsx hsy ?_
    have e1 := posFn_of_s mk w hsx
    have e2 := posFn_of_s mk w hsy
    omega

/-- The slot ends at `w`, enumerated in the loop-separating order. -/
noncomputable def endEquiv : (slotEnds C w) ≃ Fin (slotValence C w) :=
  Equiv.ofBijective (fun x => ⟨posFn mk w x.1, posFn_lt mk w x.2⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y h => Subtype.ext (posFn_inj mk w x.2 y.2 (congrArg Fin.val h)),
        by rw [Fintype.card_coe, Fintype.card_fin]; rfl⟩)

theorem endEquiv_val (x : (slotEnds C w)) :
    ((endEquiv mk w x : Fin (slotValence C w)) : ℕ) = posFn mk w (x : Fin p × Bool) := rfl

end Position

/-! ## Loop halves land on distinct centipede vertices -/

theorem legIndex_zero (D : ℕ) : legIndex D 0 = 0 := by simp [legIndex]

theorem legIndex_eq_min (D k : ℕ) (hk : k ≠ 0) :
    legIndex D k = min (k - 1) (D - 3) := by simp [legIndex, hk]

theorem legIndex_lt_legIndex {D L a b : ℕ} (hD : 4 ≤ D) (hL2 : 2 * L ≤ D)
    (hL1 : 1 ≤ L) (ha : a < L) (hb : D - L ≤ b) : legIndex D a < legIndex D b := by
  simp only [legIndex]
  split_ifs <;> omega

variable {C : Core n p} in
theorem leg_ne_loop (mk : Marking C) (w : Fin n) (hD : 4 ≤ slotValence C w)
    {x y : Fin p × Bool} (hx : x ∈ aEnds mk w) (hy : y ∈ bEnds mk w) :
    legIndex (slotValence C w) (posFn mk w x)
      ≠ legIndex (slotValence C w) (posFn mk w y) := by
  have hsplit := card_split mk w
  have hpos : 0 < (aEnds mk w).card := Finset.card_pos.mpr ⟨x, hx⟩
  have hL1 : 1 ≤ loopCount mk w := by simp only [loopCount]; omega
  have := legIndex_lt_legIndex hD (by omega) hL1 (posFn_lt_a mk w hx)
    (posFn_ge_b mk w hy)
  omega


/-! ## The expanded core -/

section Construction

variable {C : Core n p} (mk : Marking C)

/-- The valence conditions under which the marking admits a cubic expansion:
every non-marker vertex is stable, and the partner of every marker is at least
four-valent. -/
structure Stable (mk : Marking C) : Prop where
  stable : ∀ w : Fin n, ¬ mk.IsMarker w → 3 ≤ slotValence C w
  partner : ∀ j : Fin p, mk.first j = true → 4 ≤ slotValence C (C.tail j)

theorem valence_tail (hs : Stable mk) {j : Fin p} (hj : mk.second j = false) :
    3 ≤ slotValence C (C.tail j) := hs.stable _ (mk.not_isMarker_tail hj)

theorem valence_head (hs : Stable mk) {j : Fin p} (hj : mk.first j = false) :
    3 ≤ slotValence C (C.head j) := hs.stable _ (mk.not_isMarker_head hj)

theorem valence_ge_two (hs : Stable mk) (w : Fin n) : 2 ≤ slotValence C w := by
  by_cases h : mk.IsMarker w
  · obtain ⟨j, hj, hjw⟩ := h
    rw [← hjw, mk.slotValence_marker hj]
  · exact le_trans (by norm_num) (hs.stable w h)

/-- The big slot carrying a small slot: a returning loop half is carried by its
outgoing partner. -/
def carrier (j : Fin p) : Fin p := if mk.second j = true then mk.mate j else j

theorem second_carrier (j : Fin p) : mk.second (carrier mk j) = false := by
  unfold carrier
  by_cases h : mk.second j = true
  · rw [ite_eq_left h]
    exact mk.second_eq_false _ (mk.first_of_second j h)
  · rw [ite_eq_right h]
    simpa using h

theorem carrier_of_second {j : Fin p} (h : mk.second j = true) :
    carrier mk j = mk.mate j := by unfold carrier; rw [ite_eq_left h]

theorem carrier_of_not_second {j : Fin p} (h : mk.second j = false) :
    carrier mk j = j := by
  unfold carrier
  rw [ite_eq_right (by simpa using h)]

/-- The returning end of a loop, seen at the partner. -/
def mateEnd (j : Fin p) (hj : mk.first j = true) : slotEnds C (C.tail j) :=
  ⟨(mk.mate j, true), by rw [mem_slotEnds]; simpa using mk.head_mate j hj⟩

/-- The centipede vertex carrying a slot end, as a natural number. -/
def legNat (w : Fin n) (x : Fin p × Bool) : ℕ :=
  legIndex (slotValence C w) (posFn mk w x)

/-- The centipede vertex carrying a slot end. -/
def legOf (w : Fin n) (hw : 3 ≤ slotValence C w) (x : slotEnds C w) :
    Fin (slotValence C w - 2) :=
  ⟨legNat mk w (x : Fin p × Bool), legIndex_lt hw _⟩

/-- Vertices of the expansion. -/
abbrev BigV (C : Core n p) : Type := Σ w : Fin n, Fin (slotValence C w - 2)

/-- Slots of the expansion: centipede edges, plus one carrier for each small
slot that is not the returning half of a loop. -/
abbrev BigE (mk : Marking C) : Type :=
  (Σ w : Fin n, Fin (slotValence C w - 3)) ⊕ {j : Fin p // mk.second j = false}

/-- Tail endpoint of an expansion slot. -/
noncomputable def bigTail (hs : Stable mk) : BigE mk → BigV C
  | Sum.inl x => ⟨x.1, ⟨x.2.val, by have := x.2.isLt; omega⟩⟩
  | Sum.inr ⟨j, hj⟩ =>
      ⟨C.tail j, legOf mk (C.tail j) (valence_tail mk hs hj) (tailEnd C j)⟩

/-- Head endpoint of an expansion slot.  For the carrier of a loop this is a
*second* centipede vertex over the same partner. -/
noncomputable def bigHead (hs : Stable mk) : BigE mk → BigV C
  | Sum.inl x => ⟨x.1, ⟨x.2.val + 1, by have := x.2.isLt; omega⟩⟩
  | Sum.inr ⟨j, hj⟩ =>
      if hf : mk.first j = true then
        ⟨C.tail j, legOf mk (C.tail j) (by have := hs.partner j hf; omega)
          (mateEnd mk j hf)⟩
      else
        ⟨C.head j, legOf mk (C.head j) (valence_head mk hs (by simpa using hf))
          (headEnd C j)⟩

/-! ### Counting -/

/-- The markers of the marking. -/
def markerSet : Finset (Fin n) := Finset.univ.filter fun w => mk.IsMarker w

/-- The returning halves of the loops. -/
def secondSet : Finset (Fin p) := Finset.univ.filter fun j => mk.second j = true

theorem markerSet_eq_image :
    markerSet mk = (secondSet mk).image fun j => C.tail j := by
  ext w
  simp only [markerSet, secondSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨mk.mate j, mk.second_of_first j hj, mk.tail_mate j hj⟩
  · rintro ⟨j', hj', rfl⟩
    refine ⟨mk.mate j', mk.first_of_second j' hj', ?_⟩
    have h := mk.tail_mate _ (mk.first_of_second j' hj')
    rw [mk.mate_mate_second j' hj'] at h
    exact h.symm

theorem card_markerSet : (markerSet mk).card = (secondSet mk).card := by
  rw [markerSet_eq_image]
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy hxy
  simp only [Finset.mem_coe, secondSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx hy
  have hfx : mk.first (mk.mate x) = true := mk.first_of_second x hx
  have hhead : C.head (mk.mate x) = C.tail x := by
    have h := mk.tail_mate _ hfx
    rw [mk.mate_mate_second x hx] at h
    exact h.symm
  have := mk.tail_unique (mk.mate x) hfx y (by rw [hhead]; exact hxy.symm)
  rw [this, mk.mate_mate_second x hx]

theorem sum_valence_sub_two (hs : Stable mk) :
    (∑ w : Fin n, (slotValence C w - 2)) + 2 * n = 2 * p := by
  have hsum : ∑ w : Fin n, ((slotValence C w - 2) + 2)
      = ∑ w : Fin n, slotValence C w := by
    refine Finset.sum_congr rfl fun w _ => ?_
    have := valence_ge_two mk hs w
    omega
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  have hhand := sum_slotValence C
  omega

theorem sum_valence_sub_three (hs : Stable mk) :
    (∑ w : Fin n, (slotValence C w - 3)) + 3 * n
      = 2 * p + (secondSet mk).card := by
  have hsum : ∑ w : Fin n, ((slotValence C w - 3) + 3)
      = ∑ w : Fin n, (slotValence C w + (if mk.IsMarker w then 1 else 0)) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : mk.IsMarker w
    · obtain ⟨j, hj, hjw⟩ := h
      have hv : slotValence C w = 2 := by rw [← hjw]; exact mk.slotValence_marker hj
      rw [ite_eq_left ⟨j, hj, hjw⟩, hv]
    · have := hs.stable w h
      rw [ite_eq_right h]
      omega
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  have hhand := sum_slotValence C
  have hcard : ∑ w : Fin n, (if mk.IsMarker w then 1 else 0)
      = (markerSet mk).card := by
    rw [markerSet, Finset.card_filter]
  rw [hcard, card_markerSet] at hsum
  omega

theorem card_carriers :
    Fintype.card {j : Fin p // mk.second j = false} + (secondSet mk).card = p := by
  classical
  have h1 : Fintype.card {j : Fin p // mk.second j = false}
      = (Finset.univ.filter fun j : Fin p => mk.second j = false).card :=
    Fintype.card_subtype _
  have h2 : (Finset.univ.filter fun j : Fin p => mk.second j = false)
      = (Finset.univ.filter fun j : Fin p => ¬ (mk.second j = true)) := by
    refine Finset.filter_congr ?_
    intro j _
    simp
  have h3 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin p))) (p := fun j => mk.second j = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h3
  rw [h1, h2, secondSet]
  omega

theorem vertices_le_slots (hs : Stable mk) : n ≤ p := by
  have := sum_valence_sub_two mk hs
  omega

theorem card_bigV (hs : Stable mk) : Fintype.card (BigV C) = 2 * (p - n) := by
  have h := sum_valence_sub_two mk hs
  have hcard : Fintype.card (BigV C) = ∑ w : Fin n, (slotValence C w - 2) := by
    simp [Fintype.card_sigma]
  omega

theorem card_bigE (hs : Stable mk) : Fintype.card (BigE mk) = 3 * (p - n) := by
  have h2 := sum_valence_sub_two mk hs
  have h3 := sum_valence_sub_three mk hs
  have hc := card_carriers mk
  have hcard : Fintype.card (BigE mk)
      = (∑ w : Fin n, (slotValence C w - 3))
        + Fintype.card {j : Fin p // mk.second j = false} := by
    simp [Fintype.card_sum, Fintype.card_sigma]
  omega

/-! ### The expansion datum -/

/-- An indexing of the expansion vertices. -/
noncomputable def vEquiv (hs : Stable mk) : BigV C ≃ Fin (2 * (p - n)) :=
  Fintype.equivFinOfCardEq (card_bigV mk hs)

/-- An indexing of the expansion slots. -/
noncomputable def eEquiv (hs : Stable mk) : BigE mk ≃ Fin (3 * (p - n)) :=
  Fintype.equivFinOfCardEq (card_bigE mk hs)

/-- The marker-aware centipede expansion datum. -/
noncomputable def data (hs : Stable mk) :
    ExpansionData n p (2 * (p - n)) (3 * (p - n)) where
  bigCore :=
    { tail := fun e => vEquiv mk hs (bigTail mk hs ((eEquiv mk hs).symm e))
      head := fun e => vEquiv mk hs (bigHead mk hs ((eEquiv mk hs).symm e)) }
  fib := fun v => ((vEquiv mk hs).symm v).1
  kind := fun e =>
    match (eEquiv mk hs).symm e with
    | Sum.inl _ => SlotKind.contracted
    | Sum.inr j =>
        if mk.first j.1 = true then SlotKind.double j.1 (mk.mate j.1)
        else SlotKind.single j.1
  owner := fun j => eEquiv mk hs (Sum.inr ⟨carrier mk j, second_carrier mk j⟩)
  side := fun j => mk.second j

@[simp] theorem data_tail (hs : Stable mk) (a : BigE mk) :
    (data mk hs).bigCore.tail (eEquiv mk hs a) = vEquiv mk hs (bigTail mk hs a) := by
  simp [data]

@[simp] theorem data_head (hs : Stable mk) (a : BigE mk) :
    (data mk hs).bigCore.head (eEquiv mk hs a) = vEquiv mk hs (bigHead mk hs a) := by
  simp [data]

@[simp] theorem data_fib (hs : Stable mk) (x : BigV C) :
    (data mk hs).fib (vEquiv mk hs x) = x.1 := by
  simp [data]

@[simp] theorem data_kind_inl (hs : Stable mk)
    (x : Σ w : Fin n, Fin (slotValence C w - 3)) :
    (data mk hs).kind (eEquiv mk hs (Sum.inl x)) = SlotKind.contracted := by
  simp [data]

theorem data_kind_inr_first (hs : Stable mk) {j : Fin p} (hj : mk.second j = false)
    (hf : mk.first j = true) :
    (data mk hs).kind (eEquiv mk hs (Sum.inr ⟨j, hj⟩))
      = SlotKind.double j (mk.mate j) := by
  simp [data, hf]

theorem data_kind_inr_not_first (hs : Stable mk) {j : Fin p}
    (hj : mk.second j = false) (hf : mk.first j = false) :
    (data mk hs).kind (eEquiv mk hs (Sum.inr ⟨j, hj⟩)) = SlotKind.single j := by
  simp [data, hf]

@[simp] theorem data_owner (hs : Stable mk) (j : Fin p) :
    (data mk hs).owner j = eEquiv mk hs (Sum.inr ⟨carrier mk j, second_carrier mk j⟩) :=
  rfl

@[simp] theorem data_side (hs : Stable mk) (j : Fin p) :
    (data mk hs).side j = mk.second j := rfl

theorem exists_slot (hs : Stable mk) (e : Fin (3 * (p - n))) :
    ∃ a : BigE mk, eEquiv mk hs a = e :=
  ⟨(eEquiv mk hs).symm e, Equiv.apply_symm_apply _ _⟩

theorem exists_vertex (hs : Stable mk) (v : Fin (2 * (p - n))) :
    ∃ x : BigV C, vEquiv mk hs x = v :=
  ⟨(vEquiv mk hs).symm v, Equiv.apply_symm_apply _ _⟩

theorem bigTail_inr (hs : Stable mk) {j : Fin p} (hj : mk.second j = false) :
    bigTail mk hs (Sum.inr ⟨j, hj⟩)
      = ⟨C.tail j, legOf mk (C.tail j) (valence_tail mk hs hj) (tailEnd C j)⟩ := rfl

theorem bigHead_first (hs : Stable mk) {j : Fin p} (hj : mk.second j = false)
    (hf : mk.first j = true) :
    bigHead mk hs (Sum.inr ⟨j, hj⟩)
      = ⟨C.tail j, legOf mk (C.tail j) (by have := hs.partner j hf; omega)
          (mateEnd mk j hf)⟩ := by
  simp only [bigHead, dite_eq_left hf]

theorem bigHead_not_first (hs : Stable mk) {j : Fin p} (hj : mk.second j = false)
    (hf : mk.first j = false) :
    bigHead mk hs (Sum.inr ⟨j, hj⟩)
      = ⟨C.head j, legOf mk (C.head j) (valence_head mk hs hf) (headEnd C j)⟩ := by
  have hne : ¬ (mk.first j = true) := by rw [hf]; simp
  simp only [bigHead, dite_eq_right hne]

theorem tailEnd_mem_aEnds {j : Fin p} (hf : mk.first j = true) :
    ((tailEnd C j : Fin p × Bool)) ∈ aEnds mk (C.tail j) := by
  rw [mem_aEnds]
  exact ⟨rfl, rfl, hf⟩

theorem mateEnd_mem_bEnds {j : Fin p} (hf : mk.first j = true) :
    ((mateEnd mk j hf : Fin p × Bool)) ∈ bEnds mk (C.tail j) := by
  rw [mem_bEnds]
  exact ⟨mk.head_mate j hf, rfl, mk.second_of_first j hf⟩

theorem bigCore_loopless (hs : Stable mk)
    (hLoop : ∀ j : Fin p, C.tail j ≠ C.head j) (e : Fin (3 * (p - n))) :
    (data mk hs).bigCore.tail e ≠ (data mk hs).bigCore.head e := by
  obtain ⟨a, rfl⟩ := exists_slot mk hs e
  rw [data_tail, data_head]
  refine fun hEq => ?_
  have hAbs : bigTail mk hs a = bigHead mk hs a := (vEquiv mk hs).injective hEq
  cases a with
  | inl x =>
      exact absurd (congrArg (fun z : BigV C => (z.2 : ℕ)) hAbs)
        (by simp [bigTail, bigHead])
  | inr jj =>
      obtain ⟨j, hj⟩ := jj
      by_cases hf : mk.first j = true
      · rw [bigTail_inr mk hs hj, bigHead_first mk hs hj hf] at hAbs
        have hval := congrArg (fun z : BigV C => (z.2 : ℕ)) hAbs
        simp only [legOf, legNat] at hval
        exact leg_ne_loop mk (C.tail j) (hs.partner j hf)
          (tailEnd_mem_aEnds mk hf) (mateEnd_mem_bEnds mk hf) hval
      · rw [Bool.not_eq_true] at hf
        rw [bigTail_inr mk hs hj, bigHead_not_first mk hs hj hf] at hAbs
        exact hLoop j (congrArg Sigma.fst hAbs)

theorem slotCompatible (hs : Stable mk) (e : Fin (3 * (p - n))) :
    (data mk hs).SlotCompatible C e := by
  obtain ⟨a, rfl⟩ := exists_slot mk hs e
  cases a with
  | inl x =>
      refine ⟨fun _ => ?_, fun j hj => ?_, fun j₁ j₂ hj => ?_⟩
      · rw [data_tail, data_head, data_fib, data_fib]; rfl
      · rw [data_kind_inl] at hj; simp at hj
      · rw [data_kind_inl] at hj; simp at hj
  | inr jj =>
      obtain ⟨j, hj⟩ := jj
      by_cases hf : mk.first j = true
      · refine ⟨fun h => ?_, fun j' h => ?_, fun j₁ j₂ h => ?_⟩
        · rw [data_kind_inr_first mk hs hj hf] at h; simp at h
        · rw [data_kind_inr_first mk hs hj hf] at h; simp at h
        · rw [data_kind_inr_first mk hs hj hf] at h
          simp only [SlotKind.double.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, (mk.tail_mate j hf).symm, ?_⟩
          · rw [data_tail, data_fib, bigTail_inr]
          · rw [data_head, data_fib, bigHead_first mk hs hj hf]
            exact (mk.head_mate j hf).symm
      · rw [Bool.not_eq_true] at hf
        refine ⟨fun h => ?_, fun j' h => ?_, fun j₁ j₂ h => ?_⟩
        · rw [data_kind_inr_not_first mk hs hj hf] at h; simp at h
        · rw [data_kind_inr_not_first mk hs hj hf] at h
          simp only [SlotKind.single.injEq] at h
          subst h
          constructor
          · rw [data_tail, data_fib, bigTail_inr]
          · rw [data_head, data_fib, bigHead_not_first mk hs hj hf]
        · rw [data_kind_inr_not_first mk hs hj hf] at h; simp at h

theorem slotIndexed (hs : Stable mk) (e : Fin (3 * (p - n))) :
    (data mk hs).SlotIndexed e := by
  obtain ⟨a, rfl⟩ := exists_slot mk hs e
  cases a with
  | inl x =>
      exact ⟨fun j hj => by rw [data_kind_inl] at hj; simp at hj,
        fun j₁ j₂ hj => by rw [data_kind_inl] at hj; simp at hj⟩
  | inr jj =>
      obtain ⟨j, hj⟩ := jj
      by_cases hf : mk.first j = true
      · refine ⟨fun j' h => ?_, fun j₁ j₂ h => ?_⟩
        · rw [data_kind_inr_first mk hs hj hf] at h; simp at h
        · rw [data_kind_inr_first mk hs hj hf] at h
          simp only [SlotKind.double.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, hj, ?_, mk.second_of_first j hf⟩
          · rw [data_owner]
            congr 1
            refine congrArg Sum.inr (Subtype.ext ?_)
            show carrier mk j = j
            exact carrier_of_not_second mk hj
          · rw [data_owner]
            congr 1
            refine congrArg Sum.inr (Subtype.ext ?_)
            show carrier mk (mk.mate j) = j
            rw [carrier_of_second mk (mk.second_of_first j hf),
              mk.mate_mate_first j hf]
      · rw [Bool.not_eq_true] at hf
        refine ⟨fun j' h => ?_, fun j₁ j₂ h => ?_⟩
        · rw [data_kind_inr_not_first mk hs hj hf] at h
          simp only [SlotKind.single.injEq] at h
          subst h
          refine ⟨?_, hj⟩
          rw [data_owner]
          congr 1
          refine congrArg Sum.inr (Subtype.ext ?_)
          show carrier mk j = j
          exact carrier_of_not_second mk hj
        · rw [data_kind_inr_not_first mk hs hj hf] at h; simp at h

theorem slotClaimed (hs : Stable mk) (j : Fin p) : (data mk hs).SlotClaimed j := by
  by_cases hsec : mk.second j = true
  · have hfm : mk.first (mk.mate j) = true := mk.first_of_second j hsec
    have hkind : (data mk hs).kind ((data mk hs).owner j)
        = SlotKind.double (mk.mate j) j := by
      rw [data_owner]
      have hc : carrier mk j = mk.mate j := carrier_of_second mk hsec
      have hc2 : (data mk hs).kind
          (eEquiv mk hs (Sum.inr ⟨carrier mk j, second_carrier mk j⟩))
          = SlotKind.double (mk.mate j) (mk.mate (mk.mate j)) := by
        have := data_kind_inr_first mk hs (j := carrier mk j) (second_carrier mk j)
          (by rw [hc]; exact hfm)
        rw [this, hc]
      rw [hc2, mk.mate_mate_second j hsec]
    refine ⟨by rw [hkind]; simp, fun j' h => ?_, fun j₁ j₂ h => ?_⟩
    · rw [hkind] at h; simp at h
    · rw [hkind] at h
      simp only [SlotKind.double.injEq] at h
      exact Or.inr ⟨by rw [data_side, hsec], h.2.symm⟩
  · rw [Bool.not_eq_true] at hsec
    have hc : carrier mk j = j := carrier_of_not_second mk hsec
    by_cases hf : mk.first j = true
    · have hkind : (data mk hs).kind ((data mk hs).owner j)
          = SlotKind.double j (mk.mate j) := by
        rw [data_owner]
        have := data_kind_inr_first mk hs (j := carrier mk j) (second_carrier mk j)
          (by rw [hc]; exact hf)
        rw [this, hc]
      refine ⟨by rw [hkind]; simp, fun j' h => ?_, fun j₁ j₂ h => ?_⟩
      · rw [hkind] at h; simp at h
      · rw [hkind] at h
        simp only [SlotKind.double.injEq] at h
        exact Or.inl ⟨by rw [data_side, hsec], h.1.symm⟩
    · rw [Bool.not_eq_true] at hf
      have hkind : (data mk hs).kind ((data mk hs).owner j) = SlotKind.single j := by
        rw [data_owner]
        have := data_kind_inr_not_first mk hs (j := carrier mk j) (second_carrier mk j)
          (by rw [hc]; exact hf)
        rw [this, hc]
      refine ⟨by rw [hkind]; simp, fun j' h => ?_, fun j₁ j₂ h => ?_⟩
      · rw [hkind] at h
        simp only [SlotKind.single.injEq] at h
        exact ⟨by rw [data_side, hsec], h.symm⟩
      · rw [hkind] at h; simp at h

theorem markerIsolated (hs : Stable mk) (e : Fin (3 * (p - n))) :
    (data mk hs).MarkerIsolated C e := by
  obtain ⟨a, rfl⟩ := exists_slot mk hs e
  cases a with
  | inl x => exact fun j₁ j₂ h => by rw [data_kind_inl] at h; simp at h
  | inr jj =>
      obtain ⟨j, hj⟩ := jj
      by_cases hf : mk.first j = true
      · intro j₁ j₂ h
        rw [data_kind_inr_first mk hs hj hf] at h
        simp only [SlotKind.double.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        constructor
        · intro v hv
          set x := (vEquiv mk hs).symm v with hx
          have hfib : (data mk hs).fib v = x.1 := by
            rw [hx]; rfl
          rw [hfib] at hv
          have h2 : slotValence C x.1 = 2 := by
            rw [hv]; exact mk.slotValence_marker hf
          have h3 := x.2.isLt
          omega
        · exact fun j' hj' => mk.head_unique j hf j' hj'
      · intro j₁ j₂ h
        rw [Bool.not_eq_true] at hf
        rw [data_kind_inr_not_first mk hs hj hf] at h
        simp at h

theorem exists_incident (hs : Stable mk) (w : Fin n) :
    ∃ j : Fin p, C.tail j = w ∨ C.head j = w := by
  have hpos : 0 < (slotEnds C w).card := by
    have := valence_ge_two mk hs w
    unfold slotValence at this
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  refine ⟨x.1, ?_⟩
  have hx' := (mem_slotEnds C w x).mp hx
  cases hside : x.2 with
  | false => rw [hside] at hx'; simp at hx'; exact Or.inl hx'
  | true => rw [hside] at hx'; simp at hx'; exact Or.inr hx'

theorem fibre_crossing (hs : Stable mk) (T : Finset (Fin (2 * (p - n)))) (w : Fin n)
    (ia ib : Fin (slotValence C w - 2))
    (ha : vEquiv mk hs ⟨w, ia⟩ ∈ T) (hb : vEquiv mk hs ⟨w, ib⟩ ∉ T) :
    ∃ e : Fin (3 * (p - n)), (data mk hs).kind e = SlotKind.contracted ∧
      (data mk hs).fib ((data mk hs).bigCore.tail e) = w ∧
      (((data mk hs).bigCore.tail e ∈ T ∧ (data mk hs).bigCore.head e ∉ T) ∨
        ((data mk hs).bigCore.head e ∈ T ∧ (data mk hs).bigCore.tail e ∉ T)) := by
  classical
  obtain ⟨k, hk, hflip⟩ :=
    Utilities.Subdivision.TrivalentExpansion.exists_adjacent_flip
      (fun t => ∃ h : t < slotValence C w - 2, vEquiv mk hs ⟨w, ⟨t, h⟩⟩ ∈ T)
      ia.isLt ib.isLt ⟨ia.isLt, ha⟩ (by rintro ⟨h, hmem⟩; exact hb hmem)
  have hk3 : k < slotValence C w - 3 := by omega
  have hkm : k < slotValence C w - 2 := by omega
  have hk1m : k + 1 < slotValence C w - 2 := hk
  refine ⟨eEquiv mk hs (Sum.inl ⟨w, ⟨k, hk3⟩⟩), by rw [data_kind_inl], ?_, ?_⟩
  · rw [data_tail, data_fib]; rfl
  · have htail : (data mk hs).bigCore.tail (eEquiv mk hs (Sum.inl ⟨w, ⟨k, hk3⟩⟩))
        = vEquiv mk hs ⟨w, ⟨k, hkm⟩⟩ := by rw [data_tail]; rfl
    have hhead : (data mk hs).bigCore.head (eEquiv mk hs (Sum.inl ⟨w, ⟨k, hk3⟩⟩))
        = vEquiv mk hs ⟨w, ⟨k + 1, hk1m⟩⟩ := by rw [data_head]; rfl
    rw [htail, hhead]
    rcases hflip with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨_, hmem⟩ := h1
      exact Or.inl ⟨hmem, fun hcon => h2 ⟨hk1m, hcon⟩⟩
    · obtain ⟨_, hmem⟩ := h2
      exact Or.inr ⟨hmem, fun hcon => h1 ⟨hkm, hcon⟩⟩

theorem conditions (hs : Stable mk) (hLoop : ∀ j : Fin p, C.tail j ≠ C.head j) :
    (data mk hs).Conditions C := by
  classical
  refine ⟨bigCore_loopless mk hs hLoop, slotCompatible mk hs, slotIndexed mk hs,
    slotClaimed mk hs, markerIsolated mk hs, exists_incident mk hs, ?_⟩
  rintro w T ⟨a, haT, hfa⟩ ⟨b, hbT, hfb⟩
  obtain ⟨xa, rfl⟩ := exists_vertex mk hs a
  obtain ⟨xb, rfl⟩ := exists_vertex mk hs b
  obtain ⟨wa, ia⟩ := xa
  obtain ⟨wb, ib⟩ := xb
  rw [data_fib] at hfa hfb
  simp only at hfa hfb
  subst hfa
  subst hfb
  exact fibre_crossing mk hs T _ ia ib haT hbT

/-! ### The expanded core is cubic -/

theorem not_isMarker_of_fin {w : Fin n} (i : Fin (slotValence C w - 2)) :
    ¬ mk.IsMarker w := by
  rintro ⟨j, hj, rfl⟩
  have h2 := mk.slotValence_marker hj
  have h3 := i.isLt
  omega

/-- The expansion slot end attached to a small slot end. -/
noncomputable def bigEndOfEnd (hs : Stable mk) (x : Fin p × Bool) :
    Fin (3 * (p - n)) × Bool :=
  (eEquiv mk hs (Sum.inr ⟨carrier mk x.1, second_carrier mk x.1⟩), x.2)

theorem mem_slotEnds_tail (hs : Stable mk) (a : BigE mk) (x : BigV C)
    (h : bigTail mk hs a = x) :
    (eEquiv mk hs a, false) ∈ slotEnds (data mk hs).bigCore (vEquiv mk hs x) := by
  rw [mem_slotEnds]
  simpa using congrArg (vEquiv mk hs) h

theorem mem_slotEnds_head (hs : Stable mk) (a : BigE mk) (x : BigV C)
    (h : bigHead mk hs a = x) :
    (eEquiv mk hs a, true) ∈ slotEnds (data mk hs).bigCore (vEquiv mk hs x) := by
  rw [mem_slotEnds]
  simpa using congrArg (vEquiv mk hs) h

theorem bigV_eq {w : Fin n} {a b : Fin (slotValence C w - 2)} (h : a.val = b.val) :
    (⟨w, a⟩ : BigV C) = ⟨w, b⟩ := congrArg (Sigma.mk w) (Fin.val_injective h)

theorem bigV_eq' {w w' : Fin n} (hww : w = w') {a : Fin (slotValence C w - 2)}
    {b : Fin (slotValence C w' - 2)} (h : a.val = b.val) :
    (⟨w, a⟩ : BigV C) = ⟨w', b⟩ := by
  subst hww
  exact bigV_eq h

theorem head_mate_second {j : Fin p} (h : mk.second j = true) :
    C.head (mk.mate j) = C.tail j := by
  have h1 := mk.tail_mate _ (mk.first_of_second j h)
  rw [mk.mate_mate_second j h] at h1
  exact h1.symm

theorem tail_mate_second {j : Fin p} (h : mk.second j = true) :
    C.tail (mk.mate j) = C.head j := by
  have h1 := mk.head_mate _ (mk.first_of_second j h)
  rw [mk.mate_mate_second j h] at h1
  exact h1.symm

theorem mixed_absurd {w : Fin n} (hw : ¬ mk.IsMarker w) {x y : Fin p × Bool}
    (hx : x ∈ slotEnds C w) (hy : y ∈ slotEnds C w) (hs2 : x.2 = y.2)
    (hxs : mk.second x.1 = true) (hcarr : mk.mate x.1 = y.1) : False := by
  have hfy : mk.first y.1 = true := by
    rw [← hcarr]; exact mk.first_of_second _ hxs
  rw [mem_slotEnds] at hx hy
  cases hxb : x.2 with
  | false =>
      rw [hxb] at hx
      simp only [Bool.false_eq_true, ite_false] at hx
      have : C.head y.1 = w := by
        rw [← hcarr, head_mate_second mk hxs, hx]
      exact hw ⟨y.1, hfy, this⟩
  | true =>
      have hyb : y.2 = true := by rw [← hs2, hxb]
      rw [hyb] at hy
      simp only [ite_true] at hy
      exact hw ⟨y.1, hfy, hy⟩

theorem bigEndOfEnd_inj (hs : Stable mk) {w : Fin n} (hw : ¬ mk.IsMarker w)
    {x y : Fin p × Bool} (hx : x ∈ slotEnds C w) (hy : y ∈ slotEnds C w)
    (h : bigEndOfEnd mk hs x = bigEndOfEnd mk hs y) : x = y := by
  have hs2 : x.2 = y.2 := by
    have h2 : (bigEndOfEnd mk hs x).2 = (bigEndOfEnd mk hs y).2 := congrArg Prod.snd h
    exact h2
  have hcarr : carrier mk x.1 = carrier mk y.1 := by
    have h1 : (bigEndOfEnd mk hs x).1 = (bigEndOfEnd mk hs y).1 := congrArg Prod.fst h
    have he := (eEquiv mk hs).injective h1
    exact congrArg Subtype.val (Sum.inr.inj he)
  by_cases hxs : mk.second x.1 = true <;> by_cases hys : mk.second y.1 = true
  · rw [carrier_of_second mk hxs, carrier_of_second mk hys] at hcarr
    have : x.1 = y.1 := by
      rw [← mk.mate_mate_second _ hxs, hcarr, mk.mate_mate_second _ hys]
    exact Prod.ext this hs2
  · rw [Bool.not_eq_true] at hys
    rw [carrier_of_second mk hxs, carrier_of_not_second mk hys] at hcarr
    exact absurd (mixed_absurd mk hw hx hy hs2 hxs hcarr) (fun h => h)
  · rw [Bool.not_eq_true] at hxs
    rw [carrier_of_not_second mk hxs, carrier_of_second mk hys] at hcarr
    exact absurd (mixed_absurd mk hw hy hx hs2.symm hys hcarr.symm) (fun h => h)
  · rw [Bool.not_eq_true] at hxs hys
    rw [carrier_of_not_second mk hxs, carrier_of_not_second mk hys] at hcarr
    exact Prod.ext hcarr hs2

theorem bigEndOfEnd_mem (hs : Stable mk) (w : Fin n) (hw : ¬ mk.IsMarker w)
    (x : Fin p × Bool) (hx : x ∈ slotEnds C w) (i : Fin (slotValence C w - 2))
    (hleg : legNat mk w x = i.val) :
    bigEndOfEnd mk hs x ∈ slotEnds (data mk hs).bigCore (vEquiv mk hs ⟨w, i⟩) := by
  obtain ⟨j, sd⟩ := x
  rw [mem_slotEnds] at hx
  cases sd with
  | false =>
      simp only [Bool.false_eq_true, ite_false] at hx
      subst hx
      have hjs : mk.second j = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        exact hw ⟨mk.mate j, mk.first_of_second j hc, head_mate_second mk hc⟩
      have hcar : carrier mk j = j := carrier_of_not_second mk hjs
      have hstep : bigTail mk hs (Sum.inr ⟨carrier mk j, second_carrier mk j⟩)
          = ⟨C.tail j, i⟩ := by
        have hsub : (⟨carrier mk j, second_carrier mk j⟩ : {j : Fin p // mk.second j = false})
            = ⟨j, hjs⟩ := Subtype.ext hcar
        rw [hsub, bigTail_inr]
        exact bigV_eq hleg
      exact mem_slotEnds_tail mk hs _ _ hstep
  | true =>
      simp only [ite_true] at hx
      subst hx
      have hjf : mk.first j = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        exact hw ⟨j, hc, rfl⟩
      by_cases hjs : mk.second j = true
      · have hfm : mk.first (mk.mate j) = true := mk.first_of_second j hjs
        have hcar : carrier mk j = mk.mate j := carrier_of_second mk hjs
        have hsub : (⟨carrier mk j, second_carrier mk j⟩ :
            {j : Fin p // mk.second j = false})
            = ⟨mk.mate j, mk.second_eq_false _ hfm⟩ := Subtype.ext hcar
        have hstep : bigHead mk hs (Sum.inr ⟨carrier mk j, second_carrier mk j⟩)
            = ⟨C.head j, i⟩ := by
          rw [hsub, bigHead_first mk hs (mk.second_eq_false _ hfm) hfm]
          refine bigV_eq' (tail_mate_second mk hjs) ?_
          show legNat mk (C.tail (mk.mate j)) (mk.mate (mk.mate j), true) = i.val
          rw [mk.mate_mate_second j hjs, tail_mate_second mk hjs]
          exact hleg
        exact mem_slotEnds_head mk hs _ _ hstep
      · rw [Bool.not_eq_true] at hjs
        have hcar : carrier mk j = j := carrier_of_not_second mk hjs
        have hsub : (⟨carrier mk j, second_carrier mk j⟩ :
            {j : Fin p // mk.second j = false}) = ⟨j, hjs⟩ := Subtype.ext hcar
        have hstep : bigHead mk hs (Sum.inr ⟨carrier mk j, second_carrier mk j⟩)
            = ⟨C.head j, i⟩ := by
          rw [hsub, bigHead_not_first mk hs hjs hjf]
          exact bigV_eq hleg
        exact mem_slotEnds_head mk hs _ _ hstep

theorem posFn_symm (w : Fin n) (y : Fin (slotValence C w)) :
    posFn mk w (((endEquiv mk w).symm y : slotEnds C w) : Fin p × Bool) = y.val := by
  have h := endEquiv_val mk w ((endEquiv mk w).symm y)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem legEnd_mem (hs : Stable mk) (w : Fin n) (hw : ¬ mk.IsMarker w)
    (i : Fin (slotValence C w - 2)) (k : ℕ) (hkD : k < slotValence C w)
    (hk : legIndex (slotValence C w) k = i.val) :
    bigEndOfEnd mk hs (((endEquiv mk w).symm ⟨k, hkD⟩ : slotEnds C w) : Fin p × Bool)
      ∈ slotEnds (data mk hs).bigCore (vEquiv mk hs ⟨w, i⟩) := by
  refine bigEndOfEnd_mem mk hs w hw _
    ((endEquiv mk w).symm ⟨k, hkD⟩).2 i ?_
  rw [legNat, posFn_symm]
  exact hk

theorem legEnd_ne (hs : Stable mk) (w : Fin n) (hw : ¬ mk.IsMarker w) {k k' : ℕ}
    (hk : k < slotValence C w) (hk' : k' < slotValence C w) (hne : k ≠ k') :
    bigEndOfEnd mk hs (((endEquiv mk w).symm ⟨k, hk⟩ : slotEnds C w) : Fin p × Bool)
      ≠ bigEndOfEnd mk hs (((endEquiv mk w).symm ⟨k', hk'⟩ : slotEnds C w) : Fin p × Bool) := by
  intro h
  have hval := bigEndOfEnd_inj mk hs hw ((endEquiv mk w).symm ⟨k, hk⟩).2
    ((endEquiv mk w).symm ⟨k', hk'⟩).2 h
  have := (endEquiv mk w).symm.injective (Subtype.ext hval)
  exact hne (congrArg Fin.val this)

theorem legEnd_ne_contracted (hs : Stable mk) (w : Fin n) {k : ℕ}
    (hk : k < slotValence C w) (x : Σ w : Fin n, Fin (slotValence C w - 3)) (s : Bool) :
    bigEndOfEnd mk hs (((endEquiv mk w).symm ⟨k, hk⟩ : slotEnds C w) : Fin p × Bool)
      ≠ (eEquiv mk hs (Sum.inl x), s) := by
  intro h
  have hsum := (eEquiv mk hs).injective (congrArg Prod.fst h)
  simp at hsum

theorem three_le_valence (hs : Stable mk) (v : Fin (2 * (p - n))) :
    3 ≤ slotValence (data mk hs).bigCore v := by
  classical
  obtain ⟨x, rfl⟩ := exists_vertex mk hs v
  obtain ⟨w, i⟩ := x
  have hw : ¬ mk.IsMarker w := not_isMarker_of_fin mk i
  have hD := hs.stable w hw
  have hi := i.isLt
  rw [slotValence]
  by_cases hD3 : slotValence C w = 3
  · have h0 : (0 : ℕ) < slotValence C w := by omega
    have h1 : (1 : ℕ) < slotValence C w := by omega
    have h2 : (2 : ℕ) < slotValence C w := by omega
    exact three_le_card_of_three_mem
      (legEnd_ne mk hs w hw h0 h1 (by omega))
      (legEnd_ne mk hs w hw h0 h2 (by omega))
      (legEnd_ne mk hs w hw h1 h2 (by omega))
      (legEnd_mem mk hs w hw i 0 h0 (by rw [legIndex_zero]; omega))
      (legEnd_mem mk hs w hw i 1 h1 (by rw [legIndex_eq_min _ _ (by omega)]; omega))
      (legEnd_mem mk hs w hw i 2 h2 (by rw [legIndex_eq_min _ _ (by omega)]; omega))
  · by_cases hi0 : i.val = 0
    · have h0 : (0 : ℕ) < slotValence C w := by omega
      have h1 : (1 : ℕ) < slotValence C w := by omega
      have hc : (0 : ℕ) < slotValence C w - 3 := by omega
      refine three_le_card_of_three_mem
        (legEnd_ne mk hs w hw h0 h1 (by omega))
        (legEnd_ne_contracted mk hs w h0 ⟨w, ⟨0, hc⟩⟩ false)
        (legEnd_ne_contracted mk hs w h1 ⟨w, ⟨0, hc⟩⟩ false)
        (legEnd_mem mk hs w hw i 0 h0 (by rw [legIndex_zero]; omega))
        (legEnd_mem mk hs w hw i 1 h1 (by rw [legIndex_eq_min _ _ (by omega)]; omega))
        ?_
      refine mem_slotEnds_tail mk hs (Sum.inl ⟨w, ⟨0, hc⟩⟩) ⟨w, i⟩ (bigV_eq ?_)
      show (0 : ℕ) = i.val
      omega
    · by_cases hilast : i.val = slotValence C w - 3
      · have h0 : slotValence C w - 2 < slotValence C w := by omega
        have h1 : slotValence C w - 1 < slotValence C w := by omega
        have hc : i.val - 1 < slotValence C w - 3 := by omega
        refine three_le_card_of_three_mem
          (legEnd_ne mk hs w hw h0 h1 (by omega))
          (legEnd_ne_contracted mk hs w h0 ⟨w, ⟨i.val - 1, hc⟩⟩ true)
          (legEnd_ne_contracted mk hs w h1 ⟨w, ⟨i.val - 1, hc⟩⟩ true)
          (legEnd_mem mk hs w hw i (slotValence C w - 2) h0
            (by rw [legIndex_eq_min _ _ (by omega)]; omega))
          (legEnd_mem mk hs w hw i (slotValence C w - 1) h1
            (by rw [legIndex_eq_min _ _ (by omega)]; omega))
          ?_
        refine mem_slotEnds_head mk hs (Sum.inl ⟨w, ⟨i.val - 1, hc⟩⟩) ⟨w, i⟩ (bigV_eq ?_)
        show i.val - 1 + 1 = i.val
        omega
      · have h0 : i.val + 1 < slotValence C w := by omega
        have hcl : i.val - 1 < slotValence C w - 3 := by omega
        have hcr : i.val < slotValence C w - 3 := by omega
        refine three_le_card_of_three_mem
          (legEnd_ne_contracted mk hs w h0 ⟨w, ⟨i.val - 1, hcl⟩⟩ true)
          (legEnd_ne_contracted mk hs w h0 ⟨w, ⟨i.val, hcr⟩⟩ false)
          (by simp) ?_ ?_ ?_
        · exact legEnd_mem mk hs w hw i (i.val + 1) h0
            (by rw [legIndex_eq_min _ _ (by omega)]; omega)
        · refine mem_slotEnds_head mk hs (Sum.inl ⟨w, ⟨i.val - 1, hcl⟩⟩) ⟨w, i⟩
            (bigV_eq ?_)
          show i.val - 1 + 1 = i.val
          omega
        · refine mem_slotEnds_tail mk hs (Sum.inl ⟨w, ⟨i.val, hcr⟩⟩) ⟨w, i⟩ (bigV_eq ?_)
          show i.val = i.val
          rfl

theorem bigCore_cubic (hs : Stable mk) : (data mk hs).bigCore.Cubic := by
  classical
  intro v
  have hall := three_le_valence mk hs
  have hsum := sum_slotValence (data mk hs).bigCore
  have hconst : ∑ _u : Fin (2 * (p - n)), 3 = 3 * (2 * (p - n)) := by
    simp [Finset.sum_const, mul_comm]
  have hval : slotValence (data mk hs).bigCore v = 3 := by
    by_contra hne
    have hlt : 3 < slotValence (data mk hs).bigCore v := by
      have := hall v; omega
    have hstrict :
        (∑ _u : Fin (2 * (p - n)), 3) <
          ∑ u : Fin (2 * (p - n)), slotValence (data mk hs).bigCore u :=
      Finset.sum_lt_sum (fun u _ => hall u) ⟨v, Finset.mem_univ v, hlt⟩
    rw [hconst, hsum] at hstrict
    omega
  have hEq := slotValence_eq_natSum (data mk hs).bigCore v
  rw [hval] at hEq
  exact hEq.symm

/-! ### The expanded core is connected -/

theorem not_isMarker_partner (hs : Stable mk) {j : Fin p} (hf : mk.first j = true) :
    ¬ mk.IsMarker (C.tail j) := by
  rintro ⟨j', hj', hEq⟩
  have h2 := mk.slotValence_marker hj'
  rw [hEq] at h2
  have h4 := hs.partner j hf
  omega

/-- The partner of a marker; the identity on every other vertex. -/
noncomputable def partnerOf (w : Fin n) : Fin n :=
  if h : mk.IsMarker w then C.tail h.choose else w

theorem partnerOf_of_not_marker {w : Fin n} (hw : ¬ mk.IsMarker w) :
    partnerOf mk w = w := dite_eq_right hw

theorem partnerOf_marker {j : Fin p} (hj : mk.first j = true) :
    partnerOf mk (C.head j) = C.tail j := by
  have hex : mk.IsMarker (C.head j) := ⟨j, hj, rfl⟩
  rw [partnerOf, dite_eq_left hex]
  rw [mk.head_unique j hj _ hex.choose_spec.2]

theorem bigCore_connected (hs : Stable mk) (hConn : C.Connected) :
    (data mk hs).bigCore.Connected := by
  classical
  intro S hS
  obtain ⟨v0, w0, hv0, hw0⟩ := hS
  by_cases hUnif : ∀ (w : Fin n) (i i' : Fin (slotValence C w - 2)),
      vEquiv mk hs ⟨w, i⟩ ∈ S → vEquiv mk hs ⟨w, i'⟩ ∈ S
  · set S' : Finset (Fin n) := Finset.univ.filter
      (fun w => ∃ i : Fin (slotValence C (partnerOf mk w) - 2),
        vEquiv mk hs ⟨partnerOf mk w, i⟩ ∈ S) with hS'
    have hmemS' : ∀ w : Fin n, w ∈ S' ↔
        ∃ i : Fin (slotValence C (partnerOf mk w) - 2),
          vEquiv mk hs ⟨partnerOf mk w, i⟩ ∈ S := by
      intro w
      simp only [hS', Finset.mem_filter, Finset.mem_univ, true_and]
    have hmem : ∀ (w : Fin n) (i : Fin (slotValence C w - 2)),
        (vEquiv mk hs ⟨w, i⟩ ∈ S ↔ w ∈ S') := by
      intro w i
      have hw : ¬ mk.IsMarker w := not_isMarker_of_fin mk i
      rw [hmemS', partnerOf_of_not_marker mk hw]
      exact ⟨fun h => ⟨i, h⟩, fun h => hUnif w h.choose i h.choose_spec⟩
    have hsameS : ∀ j : Fin p, mk.second j = true → (C.tail j ∈ S' ↔ C.head j ∈ S') := by
      intro j hc
      have hfm := mk.first_of_second j hc
      have h1 : C.tail j = C.head (mk.mate j) := (head_mate_second mk hc).symm
      have h2 : partnerOf mk (C.tail j) = C.tail (mk.mate j) := by
        rw [h1]; exact partnerOf_marker mk hfm
      have h3 : C.tail (mk.mate j) = C.head j := tail_mate_second mk hc
      have h4 : ¬ mk.IsMarker (C.head j) := by
        rw [← h3]; exact not_isMarker_partner mk hs hfm
      rw [hmemS', hmemS', h2, h3, partnerOf_of_not_marker mk h4]
    have hsameF : ∀ j : Fin p, mk.first j = true → (C.tail j ∈ S' ↔ C.head j ∈ S') := by
      intro j hf
      have h2 : partnerOf mk (C.head j) = C.tail j := partnerOf_marker mk hf
      have h4 : ¬ mk.IsMarker (C.tail j) := not_isMarker_partner mk hs hf
      rw [hmemS', hmemS', h2, partnerOf_of_not_marker mk h4]
    obtain ⟨x0, rfl⟩ := exists_vertex mk hs v0
    obtain ⟨y0, rfl⟩ := exists_vertex mk hs w0
    obtain ⟨wv, iv⟩ := x0
    obtain ⟨ww, iw⟩ := y0
    obtain ⟨j, hj⟩ := hConn S' ⟨wv, ww, (hmem wv iv).mp hv0,
      fun hcon => hw0 ((hmem ww iw).mpr hcon)⟩
    have hjs : mk.second j = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rcases hj with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hb ((hsameS j hc).mp ha)
      · exact hb ((hsameS j hc).mpr ha)
    have hjf : mk.first j = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rcases hj with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hb ((hsameF j hc).mp ha)
      · exact hb ((hsameF j hc).mpr ha)
    refine ⟨eEquiv mk hs (Sum.inr ⟨j, hjs⟩), ?_⟩
    have htail : (data mk hs).bigCore.tail (eEquiv mk hs (Sum.inr ⟨j, hjs⟩))
        = vEquiv mk hs ⟨C.tail j,
            legOf mk (C.tail j) (valence_tail mk hs hjs) (tailEnd C j)⟩ := by
      rw [data_tail, bigTail_inr]
    have hhead : (data mk hs).bigCore.head (eEquiv mk hs (Sum.inr ⟨j, hjs⟩))
        = vEquiv mk hs ⟨C.head j,
            legOf mk (C.head j) (valence_head mk hs hjf) (headEnd C j)⟩ := by
      rw [data_head, bigHead_not_first mk hs hjs hjf]
    rw [htail, hhead, hmem, hmem]
    exact hj
  · push Not at hUnif
    obtain ⟨w, i, i', h1, h2⟩ := hUnif
    obtain ⟨e, _, _, hcross⟩ := fibre_crossing mk hs S w i i' h1 h2
    exact ⟨e, hcross⟩

/-- **Marker-aware trivalent expansion.**  A connected loopless core carrying a
marking whose markers all sit at partners of valence at least four is the target
of an equal-genus topological contraction from a *cubic loopless* connected
core of the forced size `2 (g - 1)` vertices and `3 (g - 1)` slots. -/
theorem exists_markerExpansion (hs : Stable mk)
    (hLoop : ∀ j : Fin p, C.tail j ≠ C.head j) (hConn : C.Connected) :
    ∃ D : ExpansionData n p (2 * (p - n)) (3 * (p - n)),
      D.Conditions C ∧ D.bigCore.Cubic ∧ D.bigCore.Connected :=
  ⟨data mk hs, conditions mk hs hLoop, bigCore_cubic mk hs, bigCore_connected mk hs hConn⟩

end Construction

/-! ## 6.  The stable model, at the level of specifications -/

/-- **The third move of the reduction.**  A connected marked specification whose
markers all sit at four-valent partners has a *stable model*: a specification
on a cubic loopless connected core with `2 p' = 3 n'` and the same genus,
together with the topological contraction certificate onto the given one along
which the retained relabeling transports a pencil back. -/
theorem exists_stableModel {n p : ℕ} (spec : Spec n p) (mk : Marking spec.core)
    (hs : Stable mk) (hConn : spec.core.Connected) (hGenus : n < p) :
    ∃ (n' p' : ℕ) (spec' : Spec n' p')
      (c : GraphContractionCertificate spec'.graph spec.graph),
      2 * p' = 3 * n' ∧ p' + 1 - n' = p + 1 - n ∧
        spec'.core.Cubic ∧ spec'.core.Connected ∧ c.TopologicalValid := by
  have hL := bigCore_loopless mk hs spec.core_loopless
  have hCond := conditions mk hs spec.core_loopless
  refine ⟨2 * (p - n), 3 * (p - n),
    (data mk hs).bigSpec spec (by omega) hL,
    ExpansionData.certificate (data mk hs) spec (by omega) hL,
    by omega, by omega, bigCore_cubic mk hs, bigCore_connected mk hs hConn,
    ExpansionData.certificate_topologicalValid hCond⟩

/-! ## 7.  Why the partner-valence hypothesis cannot be dropped -/

section Obstruction

variable {N Q : ℕ} {C : Core n p} {D : ExpansionData n p N Q}

/-- The two endpoints of a `double` slot lie over the two ends of the small
loop it carries. -/
theorem double_fib_eq (hCond : D.Conditions C) {e : Fin Q} {j₁ j₂ : Fin p}
    (hk : D.kind e = SlotKind.double j₁ j₂) :
    D.fib (D.bigCore.tail e) = C.tail j₁ ∧ D.fib (D.bigCore.head e) = C.head j₂ := by
  obtain ⟨-, -, h3⟩ := ExpansionData.compatible_of_conditions hCond e
  obtain ⟨ha, -, hc⟩ := h3 j₁ j₂ hk
  exact ⟨ha, hc⟩

/-- **The pendant-loop obstruction, locally.**  A `double` slot carrying a loop
at `w = C.tail j₁ = C.head j₂` has *both* endpoints in the fibre over `w`, so a
fibre with a single vertex makes it a loop of the big core, which the expansion
conditions forbid.  With the Euler identity `|fibre| = valence - 2` — forced for
every equal-genus topological contraction out of a cubic core — this says a
loop at a three-valent vertex has **no** cubic loopless expansion at the size
`2 (g-1)`, `3 (g-1)` that `dimension_forced` demands. -/
theorem not_conditions_of_singleton_fibre (hCond : D.Conditions C)
    {e : Fin Q} {j₁ j₂ : Fin p} (hk : D.kind e = SlotKind.double j₁ j₂)
    (hloop : C.tail j₁ = C.head j₂)
    (hthin : ∀ u v : Fin N, D.fib u = C.tail j₁ → D.fib v = C.tail j₁ → u = v) :
    False := by
  obtain ⟨ha, hb⟩ := double_fib_eq hCond hk
  exact ExpansionData.loopless_of_conditions hCond e
    (hthin _ _ ha (by rw [hb]; exact hloop.symm))

end Obstruction

/-! ## 8.  Non-vacuity, on both sides

`wedge_expansion` is the point of §5: the wedge of two loops at one four-valent
vertex has minimum slot valence **two**, so
`Utilities.Subdivision.TrivalentExpansion.exists_expansion` does not apply to
it, and `exists_markerExpansion` nevertheless produces the theta graph — two
vertices, three slots, cubic, loopless, connected.

`dumbbell_not_stable` is the point of §7: the dumbbell is leafless, connected
and stable in the ordinary sense (`dumbbell_base_stable`), yet its markers sit
at three-valent partners, and no cubic loopless expansion of it exists at the
size `dimension_forced` demands. -/

/-- Two loops at one four-valent vertex, displayed looplessly: vertex `0` is the
stable vertex, `1` and `2` are the markers. -/
def wedgeCore : Core 3 4 where
  tail := ![0, 1, 0, 2]
  head := ![1, 0, 2, 0]

def wedgeMarking : Marking wedgeCore where
  first := ![true, false, true, false]
  second := ![false, true, false, true]
  mate := ![1, 0, 3, 2]
  second_of_first := by decide
  first_of_second := by decide
  mate_mate_first := by decide
  mate_mate_second := by decide
  second_eq_false := by decide
  tail_mate := by decide
  head_mate := by decide
  head_unique := by decide
  tail_unique := by decide

theorem wedge_valence : slotValence wedgeCore 0 = 4 := by decide

theorem wedge_stable : Stable wedgeMarking := ⟨by decide, by decide⟩

theorem wedge_loopless : ∀ j : Fin 4, wedgeCore.tail j ≠ wedgeCore.head j := by decide

theorem wedge_connected : wedgeCore.Connected :=
  (ExplicitPotential.Core.connectedCheck_eq_true_iff wedgeCore).mp (by decide)

theorem wedge_expansion :
    ∃ D : ExpansionData 3 4 2 3,
      D.Conditions wedgeCore ∧ D.bigCore.Cubic ∧ D.bigCore.Connected :=
  exists_markerExpansion wedgeMarking wedge_stable wedge_loopless wedge_connected

theorem wedge_not_minValenceThree : ¬ (∀ w : Fin 3, 3 ≤ slotValence wedgeCore w) := by
  decide

/-- **The excluded configuration.**  A dumbbell: two one-vertex loops joined by
a bridge, displayed looplessly.  Vertices `0` and `2` are the stable vertices,
`1` and `3` the markers; slot `4` is the bridge. -/
def dumbbellCore : Core 4 5 where
  tail := ![0, 1, 2, 3, 0]
  head := ![1, 0, 3, 2, 2]

def dumbbellMarking : Marking dumbbellCore where
  first := ![true, false, true, false, false]
  second := ![false, true, false, true, false]
  mate := ![1, 0, 3, 2, 4]
  second_of_first := by decide
  first_of_second := by decide
  mate_mate_first := by decide
  mate_mate_second := by decide
  second_eq_false := by decide
  tail_mate := by decide
  head_mate := by decide
  head_unique := by decide
  tail_unique := by decide

theorem dumbbell_loopless : ∀ j : Fin 5, dumbbellCore.tail j ≠ dumbbellCore.head j := by
  decide

theorem dumbbell_connected : dumbbellCore.Connected :=
  (ExplicitPotential.Core.connectedCheck_eq_true_iff dumbbellCore).mp (by decide)

/-- The dumbbell is a legitimate output of leaf pruning and bivalent
suppression: no leaf, and every non-marker vertex is stable. -/
theorem dumbbell_base_stable :
    ∀ w : Fin 4, ¬ dumbbellMarking.IsMarker w → 3 ≤ slotValence dumbbellCore w := by
  decide

/-- **Yet it is not `Stable`.**  The partner of each marker is three-valent, and
`Stable.partner` asks for four.  This is the pendant-loop obstruction, and by
`not_conditions_of_singleton_fibre` it is not an artefact of the centipede:
the fibre over a three-valent vertex of an equal-genus contraction out of a
cubic core is a single vertex, so the loop's carrier would be a loop of the
cubic core. -/
theorem dumbbell_not_stable : ¬ Stable dumbbellMarking := by
  intro h
  have h4 := h.partner 0 (by decide)
  have h3 : slotValence dumbbellCore (dumbbellCore.tail 0) = 3 := by decide
  omega

end StableModelReduction

end DraismaVargas.LocalCases
