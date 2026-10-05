module

public import Utilities.Subdivision.SpecBridge
public import DraismaVargas.LocalCases.StableModelReduction
public import DraismaVargas.OddGenusTwoCycle
public import Utilities.Foundations.ElementaryExistence

@[expose] public section

/-!
# Bridgeless specifications admit stable models

`StableModelReduction.exists_stableModel` produces a cubic loopless stable
model of a marked specification under `Stable mk`: every non-marker vertex has
slot valence at least three, and **the partner of every marker has slot valence
at least four**.  The second clause is the pendant-loop obstruction:
`dumbbell_not_stable` shows it fails on the dumbbell, whose two markers sit at
trivalent partners.

This file removes the obstruction: contract every bridge first
(`SpecBridge.exists_bridgeless`), and transport the pencil back
(`SpecBridge.bnExists_contractBridge_iff`).

## The closing theorem

`stable_of_bridgeless`: on a **bridgeless** loopless core, every marking whose
non-marker vertices have valence at least three is `Stable`.  The argument: if
the partner `v` of a marker `w` had valence exactly
three, its third slot end would be a slot `k` whose removal separates `{v, w}`
from the rest, i.e. a bridge — the cut `{v, w}` (or its complement, depending
on the orientation of `k`) is a valid `CoreBridgeCut.Data`.  A bridgeless core
has none, so the partner is at least four-valent, which is exactly
`Stable.partner`.  `leafless_of_bridgeless` records that bridgeless cores have
no leaves either, so leaf pruning is subsumed.

## The composite

`exists_stableModel_of_bridgeless` feeds the closing theorem to
`exists_stableModel`, and `bridgeless_reduction` packages the whole reduction:
every connected specification reduces to a connected bridgeless one of the
same genus, the pencil transports back in every degree and on every uniform
refinement, and on the reduced specification every base-stable marking is
`Stable`.

## Non-vacuity

The dumbbell of `StableModelReduction` (`dumbbell_not_stable`) is the
witness: its bridge is slot `4`, contracting it gives **literally**
`wedgeCore` (`contractedDumbbell_core`, by `decide`), the wedge is
bridgeless, `stable_of_bridgeless` makes `wedgeMarking` stable through the
general route, `exists_stableModel` produces the theta graph, and the transport
carries a degree-two pencil of the wedge back to the dumbbell
(`dumbbell_bnExists_one_two`), to which `exists_stableModel` does not apply
directly.

## The odd-genus route

`OddGenusTwoCycle.extension source root` attaches a two-cycle at `root`.  When
`root` is a leaf of `source`, the extension is a lollipop and the old slot at
`root` is a bridge (`extension_isBridge_of_leaf`), so the extension is not
bridgeless (`extension_not_bridgeless_of_leaf`) and is not an admissible input
of `exists_stableModel` directly; `bridgeless_reduction` contracts that bridge
like any other.
-/

namespace DraismaVargas.LocalCases.BridgeReduction

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.PseudocorePresentation
open MarkedGraphs.Certificate
open ExplicitPotential
open DraismaVargas.LocalCases.StableModelReduction
open DraismaVargas.LocalCases.SpecBridge

/-! ## 1.  Slot ends on a bridgeless core -/

section Closing

variable {n p : ℕ} {C : Core n p}

theorem mem_slotEnds_false (k : Fin p) (v : Fin n) :
    (k, false) ∈ slotEnds C v ↔ C.tail k = v := by
  simp [mem_slotEnds]

theorem mem_slotEnds_true (k : Fin p) (v : Fin n) :
    (k, true) ∈ slotEnds C v ↔ C.head k = v := by
  simp [mem_slotEnds]

/-- A bridgeless loopless core has no leaf: a slot at a vertex of valence one
is a bridge. -/
theorem leafless_of_bridgeless (hLoop : ∀ j : Fin p, C.tail j ≠ C.head j)
    (hB : Bridgeless C) (w : Fin n) : slotValence C w ≠ 1 := by
  intro h1
  obtain ⟨⟨e, b⟩, hEnds⟩ := Finset.card_eq_one.mp h1
  have hAt : ∀ x, x ∈ slotEnds C w ↔ x = (e, b) := by
    intro x; rw [hEnds]; simp
  cases b with
  | false =>
      have hTail : C.tail e = w := (mem_slotEnds_false e w).mp ((hAt _).mpr rfl)
      apply hB e
      refine ⟨{w}, ?_, ?_, ?_⟩
      · rw [Finset.mem_singleton]; exact hTail
      · rw [Finset.mem_singleton]; intro hHead; exact hLoop e (hTail.trans hHead.symm)
      · intro k hk
        simp only [Finset.mem_singleton]
        constructor
        · intro hk'
          have := ((hAt _).mp ((mem_slotEnds_false k w).mpr hk'))
          exact absurd (congrArg Prod.fst this) hk
        · intro hk'
          have := ((hAt _).mp ((mem_slotEnds_true k w).mpr hk'))
          exact absurd (congrArg Prod.snd this) Bool.noConfusion
  | true =>
      have hHead : C.head e = w := (mem_slotEnds_true e w).mp ((hAt _).mpr rfl)
      apply hB e
      refine ⟨{w}ᶜ, ?_, ?_, ?_⟩
      · rw [Finset.mem_compl, Finset.mem_singleton]
        intro hTail; exact hLoop e (hTail.trans hHead.symm)
      · rw [Finset.mem_compl, Finset.mem_singleton, not_not]; exact hHead
      · intro k hk
        simp only [Finset.mem_compl, Finset.mem_singleton]
        constructor
        · intro _ hk'
          have := ((hAt _).mp ((mem_slotEnds_true k w).mpr hk'))
          exact hk (congrArg Prod.fst this)
        · intro _ hk'
          have := ((hAt _).mp ((mem_slotEnds_false k w).mpr hk'))
          exact absurd (congrArg Prod.snd this) Bool.noConfusion

variable (mk : Marking C)

/-- **Markings of a bridgeless core are stable.**  On a bridgeless loopless core, a
marking whose non-marker vertices have slot valence at least three is
`Stable`: the partner of every marker is at least four-valent, because a
three-valent partner would carry a bridge. -/
theorem stable_of_bridgeless (hLoop : ∀ j : Fin p, C.tail j ≠ C.head j)
    (hBase : ∀ w : Fin n, ¬ mk.IsMarker w → 3 ≤ slotValence C w)
    (hB : Bridgeless C) : Stable mk := by
  refine ⟨hBase, ?_⟩
  intro j hj
  have hvMarker : ¬ mk.IsMarker (C.tail j) := mk.not_isMarker_tail (mk.second_eq_false j hj)
  have h3 : 3 ≤ slotValence C (C.tail j) := hBase _ hvMarker
  by_contra h4
  have hcard : (slotEnds C (C.tail j)).card = 3 := by
    unfold slotValence at h3 h4; omega
  have hA : (j, false) ∈ slotEnds C (C.tail j) := (mem_slotEnds_false j _).mpr rfl
  have hB' : (mk.mate j, true) ∈ slotEnds C (C.tail j) :=
    (mem_slotEnds_true _ _).mpr (mk.head_mate j hj)
  have hAB : ((j, false) : Fin p × Bool) ≠ (mk.mate j, true) := by simp
  have hsub : ({(j, false), (mk.mate j, true)} : Finset (Fin p × Bool)) ⊆ slotEnds C (C.tail j) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hA
    · exact hB'
  have hcard2 : ({(j, false), (mk.mate j, true)} : Finset (Fin p × Bool)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  obtain ⟨⟨k, s⟩, hx⟩ :
      ((slotEnds C (C.tail j)) \ {(j, false), (mk.mate j, true)}).Nonempty := by
    have hcard3 := Finset.card_sdiff_of_subset hsub
    rw [← Finset.card_pos, hcard3, hcard, hcard2]
    norm_num
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxMem, hxNot⟩ := hx
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Prod.mk.injEq] at hxNot
  have hEnds : slotEnds C (C.tail j) = {(j, false), (mk.mate j, true), (k, s)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hA
      · exact hB'
      · exact hxMem
    · have hne1 : ((mk.mate j, true) : Fin p × Bool) ∉ ({(k, s)} : Finset (Fin p × Bool)) := by
        simp only [Finset.mem_singleton]
        intro h
        exact hxNot.2 ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
      have hne2 : ((j, false) : Fin p × Bool) ∉
          ({(mk.mate j, true), (k, s)} : Finset (Fin p × Bool)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · exact absurd (congrArg Prod.snd h) Bool.noConfusion
        · exact hxNot.1 ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
      rw [hcard, Finset.card_insert_of_notMem hne2, Finset.card_insert_of_notMem hne1,
        Finset.card_singleton]
  have hAtV : ∀ x, x ∈ slotEnds C (C.tail j) ↔
      x = (j, false) ∨ x = (mk.mate j, true) ∨ x = (k, s) := by
    intro x; rw [hEnds]; simp
  have hAtW : ∀ x, x ∈ slotEnds C (C.head j) ↔ x = (j, true) ∨ x = (mk.mate j, false) := by
    intro x; rw [mk.slotEnds_marker hj]; simp
  have hkj : k ≠ j := by
    rintro rfl
    have hs : s = true := by
      cases s
      · exact absurd ⟨rfl, rfl⟩ hxNot.1
      · rfl
    subst hs
    exact hLoop _ ((mem_slotEnds_true _ _).mp hxMem).symm
  have hkm : k ≠ mk.mate j := by
    rintro rfl
    have hs : s = false := by
      cases s
      · rfl
      · exact absurd ⟨rfl, rfl⟩ hxNot.2
    subst hs
    have := (mem_slotEnds_false _ _).mp hxMem
    rw [mk.tail_mate j hj] at this
    exact hLoop j this.symm
  -- the crossing lemma: every slot other than `k` has both ends in `{v, w}` or neither
  have hCross : ∀ k' : Fin p, k' ≠ k →
      ((C.tail k' = C.tail j ∨ C.tail k' = C.head j) ↔
        (C.head k' = C.tail j ∨ C.head k' = C.head j)) := by
    intro k' hk'
    constructor
    · rintro (hT | hT)
      · rcases (hAtV _).mp ((mem_slotEnds_false k' _).mpr hT) with h | h | h
        · rw [Prod.mk.injEq] at h; right; rw [h.1]
        · exact absurd (congrArg Prod.snd h) Bool.noConfusion
        · exact absurd (congrArg Prod.fst h) hk'
      · rcases (hAtW _).mp ((mem_slotEnds_false k' _).mpr hT) with h | h
        · exact absurd (congrArg Prod.snd h) Bool.noConfusion
        · rw [Prod.mk.injEq] at h; left; rw [h.1]; exact mk.head_mate j hj
    · rintro (hH | hH)
      · rcases (hAtV _).mp ((mem_slotEnds_true k' _).mpr hH) with h | h | h
        · exact absurd (congrArg Prod.snd h) Bool.noConfusion
        · rw [Prod.mk.injEq] at h; right; rw [h.1]; exact mk.tail_mate j hj
        · exact absurd (congrArg Prod.fst h) hk'
      · rcases (hAtW _).mp ((mem_slotEnds_true k' _).mpr hH) with h | h
        · rw [Prod.mk.injEq] at h; left; rw [h.1]
        · exact absurd (congrArg Prod.snd h) Bool.noConfusion
  apply hB k
  cases s with
  | false =>
      have hTail : C.tail k = C.tail j := (mem_slotEnds_false k _).mp hxMem
      refine ⟨{C.tail j, C.head j}, ?_, ?_, ?_⟩
      · simp [hTail]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun hEq => hLoop k (hTail.trans hEq.symm), fun hEq => ?_⟩
        rcases (hAtW _).mp ((mem_slotEnds_true k _).mpr hEq) with h | h
        · exact hkj (congrArg Prod.fst h)
        · exact absurd (congrArg Prod.snd h) Bool.noConfusion
      · intro k' hk'
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hCross k' hk'
  | true =>
      have hHead : C.head k = C.tail j := (mem_slotEnds_true k _).mp hxMem
      refine ⟨{C.tail j, C.head j}ᶜ, ?_, ?_, ?_⟩
      · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun hEq => hLoop k (hEq.trans hHead.symm), fun hEq => ?_⟩
        rcases (hAtW _).mp ((mem_slotEnds_false k _).mpr hEq) with h | h
        · exact absurd (congrArg Prod.snd h) Bool.noConfusion
        · exact hkm (congrArg Prod.fst h)
      · simp [hHead]
      · intro k' hk'
        simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
        exact not_congr (hCross k' hk')

end Closing

/-! ## 2.  Feeding the stable-model reduction -/

/-- **What `exists_stableModel` needs, supplied by bridgelessness.**  A
connected bridgeless specification of positive genus with a base-stable
marking has a stable model: a cubic loopless connected specification of the
forced size `2 p' = 3 n'`, the same genus, and a topologically valid
contraction certificate onto the given one. -/
theorem exists_stableModel_of_bridgeless {n p : ℕ} (spec : Spec n p)
    (mk : Marking spec.core)
    (hBase : ∀ w : Fin n, ¬ mk.IsMarker w → 3 ≤ slotValence spec.core w)
    (hB : Bridgeless spec.core) (hConn : spec.core.Connected) (hGenus : n < p) :
    ∃ (n' p' : ℕ) (spec' : Spec n' p')
      (c : GraphContractionCertificate spec'.graph spec.graph),
      2 * p' = 3 * n' ∧ p' + 1 - n' = p + 1 - n ∧
        spec'.core.Cubic ∧ spec'.core.Connected ∧ c.TopologicalValid :=
  exists_stableModel spec mk (stable_of_bridgeless mk spec.core_loopless hBase hB) hConn hGenus

/-- **The bridge reduction, end to end.**  Every connected specification reduces to
a connected bridgeless specification of the same genus on which every
base-stable marking is `Stable` — so `exists_stableModel` applies to it — and
the pencil transports back to the original specification, in every rank and
degree and on every uniform refinement. -/
theorem bridgeless_reduction {n p : ℕ} (spec : Spec n p) (hConn : spec.core.Connected) :
    ∃ (n' p' : ℕ) (spec' : Spec n' p'),
      spec'.core.Connected ∧ Bridgeless spec'.core ∧
      (∀ w, slotValence spec'.core w ≠ 1) ∧
      (p' : ℤ) - n' = (p : ℤ) - n ∧
      (∀ r d : ℤ, BNExists spec'.graph r d ↔ BNExists spec.graph r d) ∧
      (∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
        BNExists (spec'.scale k hk).graph r d ↔ BNExists (spec.scale k hk).graph r d) ∧
      spec'.regularSubdivisionGonality = spec.regularSubdivisionGonality ∧
      (∀ mk : Marking spec'.core,
        (∀ w, ¬ mk.IsMarker w → 3 ≤ slotValence spec'.core w) → Stable mk) := by
  obtain ⟨n', p', spec', h1, h2, -, -, h5, h6, h7⟩ := exists_bridgeless spec hConn
  exact ⟨n', p', spec', h1, h2, leafless_of_bridgeless spec'.core_loopless h2, h5, h6, h7,
    regularSubdivisionGonality_eq_of_iff spec' spec h1 hConn (fun k hk d => h7 k hk 1 d),
    fun mk hBase => stable_of_bridgeless mk spec'.core_loopless hBase h2⟩

/-! ## 3.  The dumbbell, end to end -/

/-- The dumbbell with unit lengths. -/
def dumbbellSpec : Spec 4 5 :=
  Spec.ofCore dumbbellCore (by decide) dumbbell_loopless (fun _ => 1) (fun _ => Nat.one_pos)

/-- The tail side `{0, 1}` of the bridge slot `4`. -/
def dumbbellCut : CoreBridgeCut.Data dumbbellSpec.core := ⟨{0, 1}, 4⟩

theorem dumbbellCut_valid : dumbbellCut.Valid := by decide

theorem dumbbell_isBridge : IsBridge dumbbellCore 4 := ⟨_, dumbbellCut_valid⟩

theorem dumbbell_not_bridgeless : ¬ Bridgeless dumbbellCore := fun h => h 4 dumbbell_isBridge

/-- Slot `4` is the only bridge of the dumbbell. -/
theorem dumbbell_isBridge_iff : ∀ e : Fin 5, IsBridge dumbbellCore e ↔ e = 4 := by decide

/-- The contracted dumbbell. -/
def contractedDumbbell : Spec 3 4 := contractBridge dumbbellSpec dumbbellCut dumbbellCut_valid

/-- **Contracting the bridge of the dumbbell gives the wedge of two loops**,
literally the core `wedgeCore` of `StableModelReduction`. -/
theorem contractedDumbbell_core : contractedDumbbell.core = wedgeCore := by
  show Core.mk _ _ = Core.mk _ _
  congr 1 <;> decide

theorem wedge_bridgeless : Bridgeless wedgeCore := by decide

theorem contractedDumbbell_bridgeless : Bridgeless contractedDumbbell.core := by
  rw [contractedDumbbell_core]; exact wedge_bridgeless

/-- `wedge_stable` recovered through the general route. -/
theorem wedge_stable_of_bridgeless : Stable wedgeMarking :=
  stable_of_bridgeless wedgeMarking wedge_loopless (by decide) wedge_bridgeless

/-- The marking of the contracted dumbbell: the data of `wedgeMarking`, on the
contracted core. -/
def contractedDumbbellMarking : Marking contractedDumbbell.core where
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

theorem contractedDumbbell_stable : Stable contractedDumbbellMarking :=
  stable_of_bridgeless contractedDumbbellMarking contractedDumbbell.core_loopless
    (by decide) contractedDumbbell_bridgeless

theorem contractedDumbbell_connected : contractedDumbbell.core.Connected :=
  contractBridge_connected dumbbellSpec dumbbellCut dumbbellCut_valid dumbbell_connected

/-- **The dumbbell has a stable model after all**: not directly
(`dumbbell_not_stable`), but through its bridge contraction. -/
theorem contractedDumbbell_stableModel :
    ∃ (n' p' : ℕ) (spec' : Spec n' p')
      (c : GraphContractionCertificate spec'.graph contractedDumbbell.graph),
      2 * p' = 3 * n' ∧ p' + 1 - n' = 4 + 1 - 3 ∧
        spec'.core.Cubic ∧ spec'.core.Connected ∧ c.TopologicalValid :=
  exists_stableModel contractedDumbbell contractedDumbbellMarking contractedDumbbell_stable
    contractedDumbbell_connected (by decide)

/-- The pencil transports back from the wedge to the dumbbell. -/
theorem dumbbell_transport (r d : ℤ) :
    BNExists contractedDumbbell.graph r d ↔ BNExists dumbbellSpec.graph r d :=
  bnExists_contractBridge_iff dumbbellSpec dumbbellCut dumbbellCut_valid r d

theorem contractedDumbbell_graph_connected : graph_connected contractedDumbbell.graph :=
  contractedDumbbell.graph_connected_of_coreConnected contractedDumbbell_connected

theorem contractedDumbbell_genus : genus contractedDumbbell.graph = 2 := by
  rw [Spec.genus_graph]; norm_num

/-- A degree-two pencil on the wedge of two loops, from elementary
Brill--Noether existence at genus two. -/
theorem contractedDumbbell_bnExists_one_two : BNExists contractedDumbbell.graph 1 2 := by
  apply BNExists_elementary contractedDumbbell_graph_connected
  · norm_num
  · simp [bnNumber, rectangleWidth]
  · right
    simp [rectangleWidth]

/-- **A non-trivial transport.**  The dumbbell carries a degree-two pencil,
obtained by transporting the wedge's across the contracted bridge. -/
theorem dumbbell_bnExists_one_two : BNExists dumbbellSpec.graph 1 2 :=
  (dumbbell_transport 1 2).mp contractedDumbbell_bnExists_one_two

theorem dumbbell_regularSubdivisionGonality :
    contractedDumbbell.regularSubdivisionGonality = dumbbellSpec.regularSubdivisionGonality :=
  regularSubdivisionGonality_contractBridge dumbbellSpec dumbbellCut dumbbellCut_valid
    dumbbell_connected

/-! ## 4.  The odd-genus route: the lollipop's bridge -/

section Lollipop

open DraismaVargas.OddGenusTwoCycle

theorem oldVertex_ne_markerVertex {n : ℕ} (v : Fin n) : oldVertex v ≠ markerVertex := by
  intro h
  have := congrArg Fin.val h
  simp [oldVertex, markerVertex] at this
  omega

theorem oldVertex_injective {n : ℕ} : Function.Injective (oldVertex (n := n)) :=
  fun _ _ h => Fin.castSucc_injective _ h

theorem core_tail_of_not_lt {n p : ℕ} (source : Spec n p) (root : Fin n) (k : Fin (p + 2))
    (hk : ¬ k.val < p) : (core source root).tail k = oldVertex root := by
  simp [core, hk]

theorem core_head_of_not_lt {n p : ℕ} (source : Spec n p) (root : Fin n) (k : Fin (p + 2))
    (hk : ¬ k.val < p) : (core source root).head k = markerVertex := by
  simp [core, hk]

/-- **The lollipop.**  If `root` is a leaf of `source`, with unique slot end
`(e, b)`, then the old slot `e` is a bridge of the two-cycle extension at
`root`. -/
theorem extension_isBridge_of_leaf {n p : ℕ} (source : Spec n p) (root : Fin n)
    (e : Fin p) (b : Bool) (hEnds : slotEnds source.core root = {(e, b)}) :
    IsBridge (extension source root).core (oldEdge e) := by
  have hAt : ∀ x, x ∈ slotEnds source.core root ↔ x = (e, b) := by
    intro x; rw [hEnds]; simp
  have hOther : ∀ k : Fin p, k ≠ e → source.core.tail k ≠ root ∧ source.core.head k ≠ root := by
    intro k hk
    constructor
    · intro h
      have := (hAt _).mp ((mem_slotEnds_false k root).mpr h)
      exact hk (congrArg Prod.fst this)
    · intro h
      have := (hAt _).mp ((mem_slotEnds_true k root).mpr h)
      exact hk (congrArg Prod.fst this)
  cases b with
  | false =>
      have hTail : source.core.tail e = root := (mem_slotEnds_false e root).mp ((hAt _).mpr rfl)
      refine ⟨{oldVertex root, markerVertex}, ?_, ?_, ?_⟩
      · show (core source root).tail (oldEdge e) ∈ _
        rw [core_tail_old, hTail]; simp
      · show (core source root).head (oldEdge e) ∉ _
        rw [core_head_old]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => source.core_loopless e (hTail.trans (oldVertex_injective h).symm),
          oldVertex_ne_markerVertex _⟩
      · intro k hk
        show (core source root).tail k ∈ _ ↔ (core source root).head k ∈ _
        by_cases hkp : k.val < p
        · have hke : (⟨k.val, hkp⟩ : Fin p) ≠ e := by
            intro h
            apply hk
            apply Fin.ext
            have h' := congrArg Fin.val h
            exact h'
          have hk' : k = oldEdge ⟨k.val, hkp⟩ := Fin.ext rfl
          rw [hk', core_tail_old, core_head_old]
          obtain ⟨h1, h2⟩ := hOther _ hke
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (h | h)
            · exact absurd (oldVertex_injective h) h1
            · exact absurd h (oldVertex_ne_markerVertex _)
          · rintro (h | h)
            · exact absurd (oldVertex_injective h) h2
            · exact absurd h (oldVertex_ne_markerVertex _)
        · rw [core_tail_of_not_lt source root k hkp, core_head_of_not_lt source root k hkp]
          simp
  | true =>
      have hHead : source.core.head e = root := (mem_slotEnds_true e root).mp ((hAt _).mpr rfl)
      refine ⟨{oldVertex root, markerVertex}ᶜ, ?_, ?_, ?_⟩
      · show (core source root).tail (oldEdge e) ∈ _
        rw [core_tail_old]
        simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => source.core_loopless e ((oldVertex_injective h).trans hHead.symm),
          oldVertex_ne_markerVertex _⟩
      · show (core source root).head (oldEdge e) ∉ _
        rw [core_head_old, hHead]; simp
      · intro k hk
        show (core source root).tail k ∈ _ ↔ (core source root).head k ∈ _
        by_cases hkp : k.val < p
        · have hke : (⟨k.val, hkp⟩ : Fin p) ≠ e := by
            intro h
            apply hk
            apply Fin.ext
            have h' := congrArg Fin.val h
            exact h'
          have hk' : k = oldEdge ⟨k.val, hkp⟩ := Fin.ext rfl
          rw [hk', core_tail_old, core_head_old]
          obtain ⟨h1, h2⟩ := hOther _ hke
          simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
          constructor
          · intro _
            exact ⟨fun h => h2 (oldVertex_injective h), oldVertex_ne_markerVertex _⟩
          · intro _
            exact ⟨fun h => h1 (oldVertex_injective h), oldVertex_ne_markerVertex _⟩
        · rw [core_tail_of_not_lt source root k hkp, core_head_of_not_lt source root k hkp]
          simp

/-- The two-cycle extension at a leaf is not bridgeless: it is handled by
`bridgeless_reduction`, not by `exists_stableModel` directly. -/
theorem extension_not_bridgeless_of_leaf {n p : ℕ} (source : Spec n p) (root : Fin n)
    (e : Fin p) (b : Bool) (hEnds : slotEnds source.core root = {(e, b)}) :
    ¬ Bridgeless (extension source root).core :=
  fun hB => hB _ (extension_isBridge_of_leaf source root e b hEnds)

end Lollipop

end DraismaVargas.LocalCases.BridgeReduction
