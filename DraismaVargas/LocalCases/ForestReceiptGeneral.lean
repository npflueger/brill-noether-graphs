module

public import DraismaVargas.LocalCases.CycleRows
public import DraismaVargas.LocalCases.RetainedIndexProducer
public import DraismaVargas.LocalCases.StrongRefinement
public import DraismaVargas.LocalCases.TerminalGluing

@[expose] public section

/-!
# The source zero set is a forest at a general expansion forest

**Source.**  Draisma--Vargas Part I, the proof of the main theorem (subsection
"Proof of main result"): a non-trivalent requested type is presented as a point
of the *closed* cone of a trivalent one, with zero length on exactly the
collapsed edges.  Part I does not discuss the acyclicity of the source zero set
at such a boundary point; everything below is original to this formalization,
adapted from the closed-cone reading.

## What is proved

`CycleRows.isForest_sourceZeroSet` -- the forest property at the empty
expansion forest -- runs through
`TraversalPresentation.isForest_of_cyclesAreRows`, whose arithmetic half
(`exists_notMem_sourceZeroSet_of_interface`) uses `Spec.length_pos` and so is
available only at the empty forest `F = ∅`.  At a general
`InputRefinementData.InputInterface spec presentation coordinates F` the rows
displaying the slots of `F` are contracted whole
(`InputRefinementData.sourceLength_eq_zero_of_mem_forest`), so a cycle of the
quotient source *can* sit inside the zero set as far as the arithmetic half is
concerned.  This file replaces that half.

* §1 **The census forest has a leaf.**  `exists_ends_eq_one`: a nonempty
  `ContractionForestCensusGeneral.IsForest` slot set of any `Core n p` has a
  core vertex carrying exactly one of its slot-ends.  Proved by the degree-sum
  count against the union-find class count; `ContractionForestCensusGeneral`
  has the rank inequality but no leaf.
* §2 **The datum half.**  `isForest_expansionForest`: for an
  `Utilities.Subdivision.CoreExpansion.ExpansionData` satisfying `Conditions`,
  the expansion forest `RequestedExpandedEndpoints.expansionForest D` is a
  census forest of `D.bigCore`, **given the Euler count `N + p = Q + n`**.  The
  proof identifies the contraction classes with the fibres of `D.fib`
  (`reachIn_iff_fib_eq`, from `SlotCompatible` one way and from the
  connected-fibre clause of `Conditions` the other), counts the vertices
  missing from the image of `D.fib` as the markers of the `double` slots
  (`card_image_fib_add_card_doubleSlots`), and counts the slots
  (`card_expansionForest_add_card`).  `not_isLoopy_expansionForest` is the
  loopless half.
* §3 **The source-level transfer.**  `isForest_sourceZeroSet_of_forest`:
  at a cleared face of a strong presentation with a *faithful, spanning* core
  dictionary, the zero set of the face is a census forest of the quotient
  source as soon as `F` is a census forest of `spec.core`.  A minimal
  non-forest of the zero set is a union of complete displayed rows
  (`row_subset_of_mem`, the `CycleRows` propagation started at an arbitrary
  slot); every such row has total length zero, hence lies in `F`
  (`InputRefinementData.rowSegments_sum_of_not_mem` and `Spec.length_pos`); §1
  gives that slot set a leaf; and the leaf
  vertex carries exactly one slot of the cycle, contradicting
  `TerminalForestReceipt.exists_ne_slotAt_of_minimal`.
* §4 the `Candidate.ClearedFace.SourceContractionTopology` producer at general
  `F` (`sourceContractionTopology_of_forest`, `sourceContractionTopology_of_expansion`),
  the subdivision-pencil transport with `topology` discharged
  (`exists_subdivisionPencil_of_transport_of_expansion`), and
  `exists_expansionModel_isForest`, which restates the output of the
  stable-model reduction with the datum half attached and **no Euler
  hypothesis left**.

## What is not proved here: the hypotheses, all explicit

1. `RowsMeetEndsOnly strong` (§3): *an occurrence of a displayed row incident
   to a source vertex of surviving valency ≠ 2 is the row's first occurrence at
   its start vertex or its last occurrence at its finish vertex.*  This is the
   maximality statement in the family of `StrongPresentation.head_isPathEnd`
   and `getLast_isPathEnd`, source-side only -- it mentions no specification,
   no face and no forest.  It is **not** a field of `StrongPresentation`; the
   module `RowsMeetEndsOnly` derives it (`rowsMeetEndsOnly_of_strong`) from the
   distinctness of the two ends of every row, along the lines of the closing
   note (§5).
2. `StrongRefinement.Faithful` and `StrongRefinement.Spanning` for the core
   dictionary: `StrongRefinement` §3-§4 show that `Faithful` cannot be
   derived, so both are hypotheses here, as is the dictionary
   `TraversalPresentation.CoreDictionary` itself.
3. The Euler count `N + p = Q + n` of §2.  It is genus preservation and is
   **not** implied by `ExpansionData.Conditions` (a fibre carrying a cycle
   satisfies every clause), but it holds by arithmetic for the output of the
   stable-model reduction, where `N = 2 * (p - n)` and `Q = 3 * (p - n)`
   (`RetainedIndexProducer.exists_expansionModel_retainedIndex`).
4. `NoLoopDouble` of §2, for `not_isLoopy_expansionForest` only: a `double`
   slot whose two outer ends coincide displays a genuine loop and makes
   `IsLoopy` true.  `MarkerFree` implies it; the marker-aware expansion
   `StableModelReduction.wedge_expansion` of the wedge of two loops does not
   satisfy `MarkerFree`.  This is why `ClosedContraction.ContractionData` must
   not be run at `D.bigCore`; the construction contracts the **source**
   instead, where `TerminalGluing.not_isLoopy_sourceZeroSet` supplies
   `notLoopy` unconditionally from the target.

## Consumers

`RetainedIndexProducer.terminalRetainedInputRefinement` and
`exists_subdivisionPencil_of_transport` take
`topology : Candidate.ClearedFace.SourceContractionTopology face` as a
hypothesis; §4's `sourceContractionTopology` is that hypothesis produced at a
general expansion forest.  `CycleRows.isForest_sourceZeroSet` is the `F = ∅`
instance of §3, and `CycleRows.cyclesAreRows` and
`CycleRows.row_subset_of_not_isForest` are used as they stand -- both are
quantified over every slot set.
-/

namespace DraismaVargas.LocalCases.ForestReceiptGeneral

/-! ## 1.  A nonempty census forest has a leaf -/

section Census

open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.ExplicitPotential

variable {n p : ℕ} (core : Core n p)

/-- Slot-ends of `R` at a core vertex. -/
def ends (R : Finset (Fin p)) (v : Fin n) : ℕ :=
  (R.filter fun e => core.tail e = v).card + (R.filter fun e => core.head e = v).card

/-- The vertices met by `R`. -/
def touched (R : Finset (Fin p)) : Finset (Fin n) :=
  Finset.univ.filter fun v => 0 < ends core R v

variable {core}

theorem sum_ends (R : Finset (Fin p)) :
    ∑ v : Fin n, ends core R v = 2 * R.card := by
  classical
  have hTail : R.card = ∑ v : Fin n, (R.filter fun e => core.tail e = v).card :=
    Finset.card_eq_sum_card_fiberwise (fun e _ => Finset.mem_univ (core.tail e))
  have hHead : R.card = ∑ v : Fin n, (R.filter fun e => core.head e = v).card :=
    Finset.card_eq_sum_card_fiberwise (fun e _ => Finset.mem_univ (core.head e))
  unfold ends
  rw [Finset.sum_add_distrib, ← hTail, ← hHead]
  omega

theorem mem_touched_of_mem {R : Finset (Fin p)} {e : Fin p} (he : e ∈ R) :
    core.tail e ∈ touched core R := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have : e ∈ R.filter fun f => core.tail f = core.tail e :=
    Finset.mem_filter.mpr ⟨he, rfl⟩
  have := Finset.card_pos.mpr ⟨e, this⟩
  unfold ends
  omega

theorem eq_of_reachIn_of_notMem_touched {R : Finset (Fin p)} {v w : Fin n}
    (hv : v ∉ touched core R) (h : ReachIn core R v w) : w = v := by
  classical
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      obtain ⟨e, he, hcase⟩ := hstep
      rw [mem_edgeList] at he
      refine absurd ?_ hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      unfold ends
      rcases hcase with ⟨h1, _⟩ | ⟨h1, _⟩
      · have hm : e ∈ R.filter fun f => core.tail f = v :=
          Finset.mem_filter.mpr ⟨he, h1.trans ih⟩
        have := Finset.card_pos.mpr ⟨e, hm⟩
        omega
      · have hm : e ∈ R.filter fun f => core.head f = v :=
          Finset.mem_filter.mpr ⟨he, h1.trans ih⟩
        have := Finset.card_pos.mpr ⟨e, hm⟩
        omega

theorem compFold_eq_self_of_notMem_touched {R : Finset (Fin p)} {v : Fin n}
    (hv : v ∉ touched core R) : compFold core R v = v :=
  eq_of_reachIn_of_notMem_touched hv (reachIn_self_compFold core R v)

theorem compFold_mem_touched {R : Finset (Fin p)} {v : Fin n}
    (hv : v ∈ touched core R) : compFold core R v ∈ touched core R := by
  by_contra hne
  have hback : ReachIn core R (compFold core R v) v :=
    (reachIn_equivalence core R).symm (reachIn_self_compFold core R v)
  exact hne (eq_of_reachIn_of_notMem_touched hne hback ▸ hv)

theorem card_image_add_card_touched (R : Finset (Fin p))
    (hne : (touched core R).Nonempty) :
    n + 1 ≤ (Finset.image (compFold core R) Finset.univ).card + (touched core R).card := by
  classical
  obtain ⟨t, ht⟩ := hne
  set S : Finset (Fin n) := insert (compFold core R t) (touched core R)ᶜ with hS
  have hsub : S ⊆ Finset.image (compFold core R) Finset.univ := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · rw [Finset.mem_compl] at hv
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, compFold_eq_self_of_notMem_touched hv⟩
  have hnot : compFold core R t ∉ (touched core R)ᶜ := by
    rw [Finset.mem_compl, not_not]
    exact compFold_mem_touched ht
  have hcard : S.card = (touched core R)ᶜ.card + 1 := by
    rw [hS, Finset.card_insert_of_notMem hnot]
  have hle := Finset.card_le_card hsub
  have hcompl : (touched core R)ᶜ.card + (touched core R).card = n := by
    have := Finset.card_compl (touched core R)
    have hle2 := Finset.card_le_univ (touched core R)
    simp only [Fintype.card_fin] at this hle2
    omega
  omega

/-- **A nonempty forest has a leaf.**  If the slot set `R` is a census forest
of `core` and is nonempty, some core vertex carries exactly one slot-end
of `R`.  This is the combinatorial fact the source-side transfer needs and
`ContractionForestCensusGeneral` does not have. -/
theorem exists_ends_eq_one {R : Finset (Fin p)} (hForest : IsForest core R)
    (hne : R.Nonempty) : ∃ v : Fin n, ends core R v = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨e, he⟩ := hne
  have htouched : (touched core R).Nonempty := ⟨core.tail e, mem_touched_of_mem he⟩
  have hTwo : ∀ v ∈ touched core R, 2 ≤ ends core R v := by
    intro v hv
    rw [touched, Finset.mem_filter] at hv
    have hpos := hv.2
    have := hcon v
    omega
  have hzero : ∀ v ∈ (Finset.univ : Finset (Fin n)) \ touched core R,
      ends core R v = 0 := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    have h2 := hv.2
    rw [touched, Finset.mem_filter] at h2
    by_contra hne0
    exact h2 ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hne0⟩
  have hsplit : ∑ v : Fin n, ends core R v = ∑ v ∈ touched core R, ends core R v := by
    rw [← Finset.sum_subset (Finset.subset_univ (touched core R))]
    intro v _ hv
    exact hzero v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩)
  have hbound : 2 * (touched core R).card ≤ ∑ v ∈ touched core R, ends core R v := by
    calc 2 * (touched core R).card = ∑ _v ∈ touched core R, 2 := by
          rw [Finset.sum_const, smul_eq_mul]; omega
      _ ≤ ∑ v ∈ touched core R, ends core R v := Finset.sum_le_sum hTwo
  have hsum := sum_ends (core := core) R
  have hAdd := forest_image_add_card_eq core hForest
  have hE := card_image_add_card_touched (core := core) R htouched
  omega

end Census

/-! ## 2.  The datum half: the expansion forest is a census forest -/

section Datum

open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.ExplicitPotential
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.LocalCases.RequestedExpandedEndpoints

variable {n p N Q : ℕ} {D : ExpansionData n p N Q} {C : Core n p}

/-! ### The contraction classes of the expansion forest are the fibres -/

theorem fib_eq_of_reachIn (hCond : D.Conditions C) {v w : Fin N}
    (h : ReachIn D.bigCore (expansionForest D) v w) : D.fib v = D.fib w := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      obtain ⟨e, he, hcase⟩ := hstep
      rw [mem_edgeList, mem_expansionForest] at he
      have hfib := (ExpansionData.compatible_of_conditions hCond e).1 he
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h2, ← hfib, h1, ← ih]
      · rw [← h2, hfib, h1, ← ih]

theorem reachIn_of_fib_eq (hCond : D.Conditions C) {v w : Fin N}
    (h : D.fib v = D.fib w) : ReachIn D.bigCore (expansionForest D) v w := by
  classical
  by_contra hne
  set T : Finset (Fin N) :=
    Finset.univ.filter (fun u => ReachIn D.bigCore (expansionForest D) v u) with hT
  have hvT : v ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  have hwT : w ∉ T := fun hh => hne (Finset.mem_filter.mp hh).2
  obtain ⟨e, hkc, _, hcross⟩ :=
    ExpansionData.fibre_of_conditions hCond (D.fib v) T ⟨v, hvT, rfl⟩ ⟨w, hwT, h.symm⟩
  have hstep : ReachIn D.bigCore (expansionForest D)
      (D.bigCore.tail e) (D.bigCore.head e) :=
    Relation.ReflTransGen.single
      ⟨e, (mem_edgeList _ e).mpr ((mem_expansionForest D e).mpr hkc), Or.inl ⟨rfl, rfl⟩⟩
  have hiff : D.bigCore.tail e ∈ T ↔ D.bigCore.head e ∈ T := by
    constructor
    · intro hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((Finset.mem_filter.mp hh).2).trans hstep⟩
    · intro hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((Finset.mem_filter.mp hh).2).trans
          ((reachIn_equivalence D.bigCore (expansionForest D)).symm hstep)⟩
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (hiff.mp h1)
  · exact h2 (hiff.mpr h1)

theorem reachIn_iff_fib_eq (hCond : D.Conditions C) (v w : Fin N) :
    ReachIn D.bigCore (expansionForest D) v w ↔ D.fib v = D.fib w :=
  ⟨fib_eq_of_reachIn hCond, reachIn_of_fib_eq hCond⟩

theorem compFold_eq_iff_fib_eq (hCond : D.Conditions C) (v w : Fin N) :
    compFold D.bigCore (expansionForest D) v = compFold D.bigCore (expansionForest D) w
      ↔ D.fib v = D.fib w :=
  (compFold_iff D.bigCore (expansionForest D) v w).trans (reachIn_iff_fib_eq hCond v w)

theorem card_image_compFold_eq (hCond : D.Conditions C) :
    (Finset.image (compFold D.bigCore (expansionForest D)) Finset.univ).card =
      (Finset.image D.fib Finset.univ).card := by
  classical
  refine Finset.card_bij (fun u _ => D.fib u) (fun u _ => Finset.mem_image_of_mem _
    (Finset.mem_univ u)) ?_ ?_
  · intro a ha b hb hab
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
    have hx : D.fib (compFold D.bigCore (expansionForest D) x) = D.fib x :=
      fib_eq_of_reachIn hCond
        ((reachIn_equivalence D.bigCore (expansionForest D)).symm
          (reachIn_self_compFold D.bigCore (expansionForest D) x))
    have hy : D.fib (compFold D.bigCore (expansionForest D) y) = D.fib y :=
      fib_eq_of_reachIn hCond
        ((reachIn_equivalence D.bigCore (expansionForest D)).symm
          (reachIn_self_compFold D.bigCore (expansionForest D) y))
    exact (compFold_eq_iff_fib_eq hCond x y).mpr (by rw [← hx, ← hy]; exact hab)
  · intro b hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hb
    refine ⟨compFold D.bigCore (expansionForest D) x,
      Finset.mem_image_of_mem _ (Finset.mem_univ x), ?_⟩
    exact fib_eq_of_reachIn hCond
      ((reachIn_equivalence D.bigCore (expansionForest D)).symm
        (reachIn_self_compFold D.bigCore (expansionForest D) x))

/-! ### Markers, doubles and the Euler count -/

/-- `true` exactly on the `double` slot kinds. -/
def kindIsDouble {p : ℕ} : SlotKind p → Bool
  | SlotKind.double _ _ => true
  | _ => false

/-- The big slots that carry two requested slots in series through a marker. -/
def doubleSlots (D : ExpansionData n p N Q) : Finset (Fin Q) :=
  Finset.univ.filter fun e => kindIsDouble (D.kind e)

theorem mem_doubleSlots (D : ExpansionData n p N Q) (e : Fin Q) :
    e ∈ doubleSlots D ↔ ∃ j₁ j₂ : Fin p, D.kind e = SlotKind.double j₁ j₂ := by
  classical
  simp only [doubleSlots, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hk : D.kind e with
  | contracted => simp [kindIsDouble]
  | single j => simp [kindIsDouble]
  | double j₁ j₂ => simp [kindIsDouble]

/-- The marker vertex of a `double` slot (junk on the other kinds). -/
def markerAt (D : ExpansionData n p N Q) (C : Core n p) (e : Fin Q) : Fin n :=
  match D.kind e with
  | SlotKind.double j₁ _ => C.head j₁
  | _ => D.fib (D.bigCore.tail e)

theorem markerAt_double {D : ExpansionData n p N Q} {C : Core n p} {e : Fin Q}
    {j₁ j₂ : Fin p} (hk : D.kind e = SlotKind.double j₁ j₂) :
    markerAt D C e = C.head j₁ := by
  simp only [markerAt, hk]

/-- **The contraction classes are the small core vertices that are not
markers.**  `MarkerIsolated` keeps a marker out of the fibre map's image, and
the remaining small vertices are all reached. -/
theorem card_image_fib_add_card_doubleSlots (hCond : D.Conditions C) :
    (Finset.image D.fib Finset.univ).card + (doubleSlots D).card = n := by
  classical
  have hbij : (doubleSlots D).card = (Finset.image D.fib Finset.univ)ᶜ.card := by
    refine Finset.card_bij (fun e _ => markerAt D C e) ?_ ?_ ?_
    · intro e he
      obtain ⟨j₁, j₂, hk⟩ := (mem_doubleSlots D e).mp he
      rw [Finset.mem_compl, markerAt_double hk]
      intro hmem
      obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hmem
      exact (ExpansionData.marker_of_conditions hCond e j₁ j₂ hk).1 v hv
    · intro a ha b hb hab
      obtain ⟨j₁, j₂, hka⟩ := (mem_doubleSlots D a).mp ha
      obtain ⟨j₁', j₂', hkb⟩ := (mem_doubleSlots D b).mp hb
      rw [markerAt_double hka, markerAt_double hkb] at hab
      have hj : j₁ = j₁' :=
        (ExpansionData.marker_of_conditions hCond b j₁' j₂' hkb).2 j₁ hab
      subst hj
      have h1 := (ExpansionData.owner_eq_of_double hCond hka).1
      have h2 := (ExpansionData.owner_eq_of_double hCond hkb).1
      rw [← h1, h2]
    · intro w hw
      rw [Finset.mem_compl] at hw
      have hnotfib : ∀ v : Fin N, D.fib v ≠ w := by
        intro v hv
        exact hw (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩)
      obtain ⟨j, hj⟩ := ExpansionData.incident_of_conditions hCond w
      have hcomp := ExpansionData.compatible_of_conditions hCond (D.owner j)
      rcases ExpansionData.exists_carrier hCond j with ⟨hk, -⟩ | ⟨j₂, hk, -⟩ | ⟨j₁, hk, -⟩
      · obtain ⟨hT, hH⟩ := hcomp.2.1 j hk
        rcases hj with h | h
        · exact absurd (hT.trans h) (hnotfib _)
        · exact absurd (hH.trans h) (hnotfib _)
      · obtain ⟨hT, hM, hH⟩ := hcomp.2.2 j j₂ hk
        rcases hj with h | h
        · exact absurd (hT.trans h) (hnotfib _)
        · exact ⟨D.owner j, (mem_doubleSlots D _).mpr ⟨j, j₂, hk⟩,
            (markerAt_double hk).trans h⟩
      · obtain ⟨hT, hM, hH⟩ := hcomp.2.2 j₁ j hk
        rcases hj with h | h
        · exact ⟨D.owner j, (mem_doubleSlots D _).mpr ⟨j₁, j, hk⟩,
            (markerAt_double hk).trans (hM.trans h)⟩
        · exact absurd (hH.trans h) (hnotfib _)
  have hcompl := Finset.card_compl (Finset.image D.fib Finset.univ)
  simp only [Fintype.card_fin] at hcompl
  have hle := Finset.card_le_univ (Finset.image D.fib (Finset.univ : Finset (Fin N)))
  simp only [Fintype.card_fin] at hle
  omega

/-- Fibre of the `owner` map over one big slot. -/
theorem card_owner_fibre (hCond : D.Conditions C) (e : Fin Q) :
    (Finset.univ.filter fun j : Fin p => D.owner j = e).card +
        (if D.kind e = SlotKind.contracted then 1 else 0) =
      1 + (if kindIsDouble (D.kind e) then 1 else 0) := by
  classical
  cases hk : D.kind e with
  | contracted =>
      have hempty : (Finset.univ.filter fun j : Fin p => D.owner j = e) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem ?_
        intro j hj
        have hj' := (Finset.mem_filter.mp hj).2
        exact (ExpansionData.claimed_of_conditions hCond j).1 (by rw [hj', hk])
      rw [hempty]
      simp [kindIsDouble]
  | single j₀ =>
      have hsingleton : (Finset.univ.filter fun j : Fin p => D.owner j = e) = {j₀} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hj
          have hc := ExpansionData.claimed_of_conditions hCond j
          exact ((hc.2.1 j₀ (by rw [hj, hk])).2).symm
        · rintro rfl
          exact (ExpansionData.owner_eq_of_single hCond hk).1
      rw [hsingleton]
      simp [kindIsDouble]
  | double j₁ j₂ =>
      have hne : j₁ ≠ j₂ := by
        obtain ⟨-, hs1, -, hs2⟩ := (ExpansionData.indexed_of_conditions hCond e).2 j₁ j₂ hk
        intro h
        rw [h, hs2] at hs1
        exact Bool.noConfusion hs1
      have hpair : (Finset.univ.filter fun j : Fin p => D.owner j = e) = {j₁, j₂} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hj
          have hc := ExpansionData.claimed_of_conditions hCond j
          rcases hc.2.2 j₁ j₂ (by rw [hj, hk]) with ⟨-, h⟩ | ⟨-, h⟩
          · exact Or.inl h.symm
          · exact Or.inr h.symm
        · obtain ⟨h1, -, h2, -⟩ := ExpansionData.owner_eq_of_double hCond hk
          rintro (rfl | rfl)
          · exact h1
          · exact h2
      rw [hpair, Finset.card_insert_of_notMem (by simpa using hne)]
      simp [kindIsDouble]

/-- **The slot count.**  Every requested slot is carried by exactly one
non-contracted big slot, a `double` carrying two. -/
theorem card_expansionForest_add_card (hCond : D.Conditions C) :
    (expansionForest D).card + p = Q + (doubleSlots D).card := by
  classical
  have hp : p = ∑ e : Fin Q, (Finset.univ.filter fun j : Fin p => D.owner j = e).card := by
    have := Finset.card_eq_sum_card_fiberwise
      (f := D.owner) (s := (Finset.univ : Finset (Fin p)))
      (t := (Finset.univ : Finset (Fin Q))) (fun j _ => Finset.mem_univ _)
    simpa using this
  have hF : (expansionForest D).card =
      ∑ e : Fin Q, (if D.kind e = SlotKind.contracted then 1 else 0) := by
    rw [expansionForest, Finset.card_filter]
  have hD : (doubleSlots D).card =
      ∑ e : Fin Q, (if kindIsDouble (D.kind e) then 1 else 0) := by
    rw [doubleSlots, Finset.card_filter]
  have hQ : Q = ∑ _e : Fin Q, 1 := by simp
  have hsum : (∑ e : Fin Q, (if D.kind e = SlotKind.contracted then 1 else 0)) +
      (∑ e : Fin Q, (Finset.univ.filter fun j : Fin p => D.owner j = e).card) =
      (∑ _e : Fin Q, 1) +
        (∑ e : Fin Q, (if kindIsDouble (D.kind e) then 1 else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := card_owner_fibre hCond e
    omega
  omega

/-- **The datum half.**  The expansion forest of an expansion datum
satisfying the `Conditions` is a census forest of the expanded core, as soon as
the Euler count `N + p = Q + n` holds.  The Euler count is exactly genus
preservation and is *not* implied by `Conditions`. -/
theorem isForest_expansionForest (hCond : D.Conditions C) (hEuler : N + p = Q + n) :
    IsForest D.bigCore (expansionForest D) := by
  classical
  have h1 := card_image_compFold_eq hCond
  have h2 := card_image_fib_add_card_doubleSlots hCond
  have h3 := card_expansionForest_add_card hCond
  unfold IsForest
  omega

/-! ### The loopless half -/

/-- **No `double` slot of the datum carries a loop of the requested core.**  A
`double` displays a loop of the requested metric graph looplessly, through its
marker; when its two outer ends coincide the expanded slot becomes a loop after
the forest is contracted, and `IsLoopy` holds.  `MarkerFree` implies this
vacuously. -/
def NoLoopDouble (D : ExpansionData n p N Q) (C : Core n p) : Prop :=
  ∀ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e = SlotKind.double j₁ j₂ →
    C.tail j₁ ≠ C.head j₂

instance decidableNoLoopDouble (D : ExpansionData n p N Q) (C : Core n p) :
    Decidable (NoLoopDouble D C) := by
  unfold NoLoopDouble; infer_instance

theorem noLoopDouble_of_markerFree
    (hMF : DraismaVargas.LocalCases.RetainedIndexProducer.MarkerFree D) :
    NoLoopDouble D C :=
  fun e j₁ j₂ hk => absurd hk (hMF e j₁ j₂)

/-- **The loopless half.**  Contracting the expansion forest leaves no
surviving big slot a loop, provided the requested core is loopless and no
`double` carries a loop. -/
theorem not_isLoopy_expansionForest (hCond : D.Conditions C)
    (hLoopless : ∀ j : Fin p, C.tail j ≠ C.head j) (hND : NoLoopDouble D C) :
    ¬ IsLoopy D.bigCore (expansionForest D) := by
  rintro ⟨e, he, heq⟩
  rw [mem_expansionForest] at he
  have hfib : D.fib (D.bigCore.tail e) = D.fib (D.bigCore.head e) :=
    (compFold_eq_iff_fib_eq hCond _ _).mp heq
  have hcomp := ExpansionData.compatible_of_conditions hCond e
  cases hk : D.kind e with
  | contracted => exact he hk
  | single j =>
      obtain ⟨hT, hH⟩ := hcomp.2.1 j hk
      exact hLoopless j (by rw [← hT, ← hH, hfib])
  | double j₁ j₂ =>
      obtain ⟨hT, -, hH⟩ := hcomp.2.2 j₁ j₂ hk
      exact hND e j₁ j₂ hk (by rw [← hT, ← hH, hfib])

/-! ### Non-vacuity: the banana expansion -/

open DraismaVargas.LocalCases.RequestedExpandedEndpoints in
theorem banana_isForest :
    IsForest bananaExpansion.bigCore (expansionForest bananaExpansion) :=
  isForest_expansionForest (C := bananaCore) banana_conditions (by norm_num)

open DraismaVargas.LocalCases.RequestedExpandedEndpoints in
theorem banana_noLoopDouble : NoLoopDouble bananaExpansion bananaCore := by decide

open DraismaVargas.LocalCases.RequestedExpandedEndpoints in
theorem banana_not_isLoopy :
    ¬ IsLoopy bananaExpansion.bigCore (expansionForest bananaExpansion) :=
  not_isLoopy_expansionForest (C := bananaCore) banana_conditions
    bananaSpec.core_loopless banana_noLoopDouble

end Datum

/-! ## 3.  The source-level transfer

A minimal non-forest of the quotient source's zero set is a union of *complete*
displayed rows -- that is `CycleRows`' propagation argument, restated here so
that it may be started at an arbitrary slot of the cycle rather than at one
chosen slot (`row_subset_of_mem`).  Each such row has all its occurrences in
the zero set, so its total cleared length is zero, so by
`InputRefinementData.rowSegments_sum_of_not_mem` and `Spec.length_pos` its slot
lies in the forest `F`.  §1 gives the resulting subset of `F` a leaf, and at
the leaf's quotient-source vertex the cycle has only one incidence, which
`TerminalForestReceipt.exists_ne_slotAt_of_minimal` forbids. -/

section Source

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.PresentationDecomposition
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ZeroForestBridge
open DraismaVargas.LocalCases.ZeroForestPreservation
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.LocalCases.CycleRows (mem_of_meetsAt meetsAt_symm slotAt_iff_incident
  core_loopless)
open DraismaVargas.LocalCases.TerminalForestReceipt (SlotAt exists_minimal_not_isForest
  exists_ne_slotAt_of_minimal notMem_of_separated)
open DraismaVargas.LocalCases.ZeroFreeTerminalFace (isForest_empty)

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ} {spec : Spec n p} {F : Finset (Fin p)}

/-- A property constant along the steps of a chain is constant on the chain.
(`CycleRows`' private helper, restated; it is a fact about lists.) -/
private theorem forall_mem_iff_of_isChain {α : Type*} {R : α → α → Prop}
    {P : α → Prop} :
    ∀ L : List α, L.IsChain R → (∀ a ∈ L, ∀ b ∈ L, R a b → (P a ↔ P b)) →
      ∀ a ∈ L, ∀ b ∈ L, (P a ↔ P b) := by
  intro L
  induction L with
  | nil => intro _ _ a ha; simp at ha
  | cons x xs ih =>
    intro hChain hStep
    have hKey : ∀ b ∈ x :: xs, (P x ↔ P b) := by
      intro b hb
      match xs, hChain with
      | [], _ =>
        rw [List.mem_singleton] at hb
        exact hb ▸ Iff.rfl
      | y :: ys, hChain =>
        rw [List.isChain_cons_cons] at hChain
        have hHead : P x ↔ P y := hStep x (by simp) y (by simp) hChain.1
        have hTail := ih hChain.2
          (fun a ha b hb hab ↦ hStep a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb) hab)
        rcases List.mem_cons.mp hb with hb | hb
        · exact hb ▸ Iff.rfl
        · exact hHead.trans (hTail y (by simp) b hb)
    exact fun a ha b hb ↦ (hKey a ha).symm.trans (hKey b hb)

/-- **The propagation, started anywhere.**  A minimal non-forest containing one
occurrence of a displayed row contains the whole row.  This is the body of
`CycleRows.row_subset_of_not_isForest` with the starting slot left free. -/
theorem row_subset_of_mem
    {presentation : data.LengthMatrixPresentation coordinate}
    (hDecomposes : Decomposes presentation)
    (hChain : ∀ row : coordinate, (presentation.path row).IsChain (MeetsAt data))
    (realization : data.NonnegativeIntegralRealization)
    {C : Finset (Fin data.sourceGraph.edges.card)}
    (hNot : ¬ IsForest (UnitSubdivisionPresentation.core data.sourceGraph) C)
    (hMin : ∀ drop ∈ C,
      IsForest (UnitSubdivisionPresentation.core data.sourceGraph) (C.erase drop))
    (hSurvive : ∀ slot ∈ C, ¬ IsDangling data (realization.sourceEdgeAt slot))
    {row : coordinate} {seed : data.SourceEdge}
    (hSeedMem : seed ∈ presentation.path row)
    (hSeedC : slotOf data realization seed ∈ C) :
    ∀ edge ∈ presentation.path row, slotOf data realization edge ∈ C := by
  have hNonDangling : ∀ edge ∈ presentation.path row, ¬ IsDangling data edge :=
    fun edge hEdge hDangling ↦ hDecomposes.dangling_not_mem edge hDangling row hEdge
  have hConstant := forall_mem_iff_of_isChain
    (P := fun edge ↦ slotOf data realization edge ∈ C)
    (presentation.path row) (hChain row)
    (fun a ha b hb hab ↦
      ⟨fun hA ↦ mem_of_meetsAt realization hNot hMin hSurvive
          (hNonDangling a ha) (hNonDangling b hb) hab hA,
        fun hB ↦ mem_of_meetsAt realization hNot hMin hSurvive
          (hNonDangling b hb) (hNonDangling a ha) (meetsAt_symm hab) hB⟩)
  intro edge hEdge
  exact (hConstant seed hSeedMem edge hEdge).mp hSeedC

/-! ### The row-end census, from one source-side hypothesis -/

section Dictionary

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ} {spec : Spec n p} {F : Finset (Fin p)}

/-- **The source-side hypothesis: displayed rows meet non-bivalent
vertices only at their own ends.**  An occurrence of a displayed row incident
to a quotient-source vertex of surviving valency different from two is the
row's *first* occurrence, met at its start vertex, or its *last* occurrence,
met at its finish vertex.

This is the maximality statement in the family of
`TraversalPresentation.StrongPresentation.head_isPathEnd` and `getLast_isPathEnd`
-- purely source-side: it mentions no specification, no face and no forest --
and it is exactly what those two fields stop short of.  It is *not* a field of
`StrongPresentation`; the module `RowsMeetEndsOnly` derives it, along the lines
of the closing note (§5). -/
def RowsMeetEndsOnly (strong : StrongPresentation candidate.datum coordinate) : Prop :=
  ∀ (row : coordinate) (edge : candidate.datum.SourceEdge),
    edge ∈ strong.toPresentation.path row →
    ∀ u : candidate.datum.SourceVertex, Incident candidate.datum edge u →
      nonDanglingValency candidate.datum u ≠ 2 →
      (u = strong.start row ∧ edge ∈ (strong.toPresentation.path row).head?) ∨
        (u = strong.finish row ∧ edge ∈ (strong.toPresentation.path row).getLast?)

/-- The hypothesis is not self-contradictory: it holds vacuously on a datum whose
quotient source is a disjoint union of cycles, where no vertex has surviving
valency different from two. -/
theorem rowsMeetEndsOnly_of_valency_two
    {strong : StrongPresentation candidate.datum coordinate}
    (hValency : ∀ u : candidate.datum.SourceVertex,
      nonDanglingValency candidate.datum u = 2) :
    RowsMeetEndsOnly strong :=
  fun _ _ _ u _ hne ↦ absurd (hValency u) hne

/-- Every row has a first occurrence. -/
theorem exists_head (strong : StrongPresentation candidate.datum coordinate)
    (row : coordinate) :
    ∃ edge, (strong.toPresentation.path row).head? = some edge := by
  rcases hEq : (strong.toPresentation.path row).head? with _ | edge
  · exact absurd (List.head?_eq_none_iff.mp hEq) (strong.path_ne_nil row)
  · exact ⟨edge, rfl⟩

/-- Every row has a last occurrence. -/
theorem exists_getLast (strong : StrongPresentation candidate.datum coordinate)
    (row : coordinate) :
    ∃ edge, (strong.toPresentation.path row).getLast? = some edge := by
  rcases hEq : (strong.toPresentation.path row).getLast? with _ | edge
  · exact absurd (List.getLast?_eq_none_iff.mp hEq) (strong.path_ne_nil row)
  · exact ⟨edge, rfl⟩

/-- **A placed stable core vertex is never bivalent.**  A spanning dictionary
puts every stable core vertex at the start or finish of a displayed row, and
those are `IsPathEnd` vertices. -/
theorem nonDanglingValency_vertexAt_ne_two
    {strong : StrongPresentation candidate.datum coordinate}
    {iface : InputInterface spec strong.toPresentation coordinates F}
    (dict : CoreDictionary spec strong iface) (hSpanning : Spanning dict)
    (v : Fin n) :
    nonDanglingValency candidate.datum (dict.vertexAt v) ≠ 2 := by
  rcases hSpanning v with ⟨i, hi⟩ | ⟨i, hi⟩
  · obtain ⟨edge, hedge⟩ := exists_head strong (iface.slot i)
    rw [hi]
    exact (strong.head_isPathEnd (iface.slot i) edge (by rw [hedge]; rfl)).2
  · obtain ⟨edge, hedge⟩ := exists_getLast strong (iface.slot i)
    rw [hi]
    exact (strong.getLast_isPathEnd (iface.slot i) edge (by rw [hedge]; rfl)).2

/-- **The census, half one.**  An occurrence of the row displaying slot `i`
incident to the quotient-source vertex carrying the stable core vertex `v` puts
an end of `i` at `v`. -/
theorem end_of_incident
    {strong : StrongPresentation candidate.datum coordinate}
    {iface : InputInterface spec strong.toPresentation coordinates F}
    (dict : CoreDictionary spec strong iface)
    (hFaithful : Faithful dict) (hSpanning : Spanning dict)
    (hRows : RowsMeetEndsOnly strong)
    {v : Fin n} {i : Fin p} {edge : candidate.datum.SourceEdge}
    (hedge : edge ∈ strong.toPresentation.path (iface.slot i))
    (hinc : Incident candidate.datum edge (dict.vertexAt v)) :
    spec.core.tail i = v ∨ spec.core.head i = v := by
  rcases hRows (iface.slot i) edge hedge (dict.vertexAt v) hinc
      (nonDanglingValency_vertexAt_ne_two dict hSpanning v) with ⟨hu, -⟩ | ⟨hu, -⟩
  · exact Or.inl (hFaithful ((dict.tail_eq i).trans hu.symm))
  · exact Or.inr (hFaithful ((dict.head_eq i).trans hu.symm))

/-- **The census, half two.**  At a stable core vertex carrying exactly one end
of slot `i`, the row displaying `i` has exactly one incident occurrence. -/
theorem unique_at_simple_end
    {strong : StrongPresentation candidate.datum coordinate}
    {iface : InputInterface spec strong.toPresentation coordinates F}
    (dict : CoreDictionary spec strong iface)
    (hFaithful : Faithful dict) (hSpanning : Spanning dict)
    (hRows : RowsMeetEndsOnly strong)
    {v : Fin n} {i : Fin p}
    (hsimple : (spec.core.tail i = v ∧ spec.core.head i ≠ v) ∨
      (spec.core.head i = v ∧ spec.core.tail i ≠ v))
    {first second : candidate.datum.SourceEdge}
    (hFirst : first ∈ strong.toPresentation.path (iface.slot i))
    (hSecond : second ∈ strong.toPresentation.path (iface.slot i))
    (hIncFirst : Incident candidate.datum first (dict.vertexAt v))
    (hIncSecond : Incident candidate.datum second (dict.vertexAt v)) :
    first = second := by
  have hval := nonDanglingValency_vertexAt_ne_two dict hSpanning v
  rcases hsimple with ⟨hTail, hHead⟩ | ⟨hHead, hTail⟩
  · have hStart : dict.vertexAt v = strong.start (iface.slot i) := by
      rw [← hTail]; exact dict.tail_eq i
    have hFin : dict.vertexAt v ≠ strong.finish (iface.slot i) := by
      intro hh
      exact hHead (hFaithful ((dict.head_eq i).trans hh.symm))
    have hOne := hRows (iface.slot i) first hFirst _ hIncFirst hval
    have hTwo := hRows (iface.slot i) second hSecond _ hIncSecond hval
    rcases hOne with ⟨-, h1⟩ | ⟨hbad, -⟩
    · rcases hTwo with ⟨-, h2⟩ | ⟨hbad, -⟩
      · rw [Option.mem_def] at h1 h2
        exact Option.some_inj.mp (h1.symm.trans h2)
      · exact absurd hbad hFin
    · exact absurd hbad hFin
  · have hFin : dict.vertexAt v = strong.finish (iface.slot i) := by
      rw [← hHead]; exact dict.head_eq i
    have hStart : dict.vertexAt v ≠ strong.start (iface.slot i) := by
      intro hh
      exact hTail (hFaithful ((dict.tail_eq i).trans hh.symm))
    have hOne := hRows (iface.slot i) first hFirst _ hIncFirst hval
    have hTwo := hRows (iface.slot i) second hSecond _ hIncSecond hval
    rcases hOne with ⟨hbad, -⟩ | ⟨-, h1⟩
    · exact absurd hbad hStart
    · rcases hTwo with ⟨hbad, -⟩ | ⟨-, h2⟩
      · exact absurd hbad hStart
      · rw [Option.mem_def] at h1 h2
        exact Option.some_inj.mp (h1.symm.trans h2)

/-- **A faithful dictionary gives every row two distinct ends.**  This is what
the length-one case of `RowsMeetEndsOnly` needs, and it *is* available: it is
`Spec.core_loopless` read through `Faithful`. -/
theorem start_ne_finish
    {strong : StrongPresentation candidate.datum coordinate}
    {iface : InputInterface spec strong.toPresentation coordinates F}
    (dict : CoreDictionary spec strong iface) (hFaithful : Faithful dict)
    (i : Fin p) :
    strong.start (iface.slot i) ≠ strong.finish (iface.slot i) := by
  intro h
  exact spec.core_loopless i
    (hFaithful ((dict.tail_eq i).trans (h.trans (dict.head_eq i).symm)))

end Dictionary

/-! ### The transfer -/

section Transfer

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ} {spec : Spec n p} {F : Finset (Fin p)}

/-- **The zero set is a forest at a general expansion forest.**  If the forest
`F` is a census forest of the stable core, the zero set of a cleared face of a
strong presentation carrying a faithful, spanning core dictionary is a census
forest of the quotient source.

At `F = ∅` this is `CycleRows.isForest_sourceZeroSet` (which needs none of the
dictionary hypotheses, the arithmetic half being free there); the content here
is that the forest rows, which *are* swallowed by the zero set, cannot close up
into a cycle. -/
theorem isForest_sourceZeroSet_of_forest
    (strong : StrongPresentation candidate.datum coordinate)
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (dict : CoreDictionary spec strong iface)
    (hFaithful : Faithful dict) (hSpanning : Spanning dict)
    (hRows : RowsMeetEndsOnly strong)
    (hForest : IsForest spec.core F) :
    IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet := by
  classical
  by_contra hNotForest
  obtain ⟨C, hSubset, hNot, hMin⟩ :=
    exists_minimal_not_isForest
      (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet hNotForest
  have hSurvive : ∀ slot ∈ C,
      ¬ IsDangling candidate.datum (face.realization.sourceEdgeAt slot) := by
    intro slot hSlot hDangling
    exact notMem_of_separated _ hNot hMin
      (fun G ↦ DraismaVargas.LocalCases.CycleRows.not_reachIn_of_isDangling
        candidate.datum face.realization hDangling G rfl) hSlot
  have hZero : ∀ edge : candidate.datum.SourceEdge,
      slotOf candidate.datum face.realization edge ∈ C →
      face.realization.sourceLength edge = 0 := by
    intro edge hMem
    have h := (face.realization.mem_sourceZeroSet _).mp (hSubset hMem)
    simpa only [sourceEdgeAt_slotOf] using h
  obtain ⟨seed, hSeed⟩ : C.Nonempty := by
    rcases C.eq_empty_or_nonempty with rfl | hNonempty
    · exact absurd (isForest_empty _) hNot
    · exact hNonempty
  set R : Finset (Fin p) := Finset.univ.filter (fun i : Fin p ↦
    ∃ edge ∈ strong.toPresentation.path (iface.slot i),
      slotOf candidate.datum face.realization edge ∈ C) with hRdef
  have hRmem : ∀ i : Fin p, i ∈ R ↔
      ∃ edge ∈ strong.toPresentation.path (iface.slot i),
        slotOf candidate.datum face.realization edge ∈ C := by
    intro i
    rw [hRdef, Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩
  have hRowSub : ∀ i ∈ R, ∀ edge ∈ strong.toPresentation.path (iface.slot i),
      slotOf candidate.datum face.realization edge ∈ C := by
    intro i hi
    obtain ⟨seedEdge, hSeedMem, hSeedC⟩ := (hRmem i).mp hi
    exact row_subset_of_mem strong.decomposes strong.chain face.realization hNot hMin
      hSurvive hSeedMem hSeedC
  have hRF : R ⊆ F := by
    intro i hi
    by_contra hnot
    have hall : ∀ x ∈ rowSegments iface face i, x = 0 := by
      intro x hx
      obtain ⟨edge, hedge, hxe⟩ := List.mem_map.mp hx
      rw [← hxe]
      exact hZero edge (hRowSub i hi edge hedge)
    have hsum : (rowSegments iface face i).sum = 0 := List.sum_eq_zero hall
    rw [rowSegments_sum_of_not_mem iface face hnot] at hsum
    have hpos : 0 < face.scale * spec.length i :=
      Nat.mul_pos face.scale_pos (spec.length_pos i)
    omega
  have hRne : R.Nonempty := by
    obtain ⟨row, hrow⟩ := strong.decomposes.surviving_mem
      (face.realization.sourceEdgeAt seed) (hSurvive seed hSeed)
    refine ⟨iface.slot.symm row, (hRmem _).mpr ⟨face.realization.sourceEdgeAt seed, ?_, ?_⟩⟩
    · rw [Equiv.apply_symm_apply]; exact hrow
    · rw [slotOf_sourceEdgeAt]; exact hSeed
  obtain ⟨v, hv⟩ := exists_ends_eq_one
    (ZeroForestBridge.isForest_of_subset spec.core hRF hForest) hRne
  have hAB : (R.filter fun e ↦ spec.core.tail e = v).card
      + (R.filter fun e ↦ spec.core.head e = v).card = 1 := hv
  have hmemA : ∀ j ∈ R, spec.core.tail j = v →
      j ∈ R.filter fun e ↦ spec.core.tail e = v :=
    fun j hj hh ↦ Finset.mem_filter.mpr ⟨hj, hh⟩
  have hmemB : ∀ j ∈ R, spec.core.head j = v →
      j ∈ R.filter fun e ↦ spec.core.head e = v :=
    fun j hj hh ↦ Finset.mem_filter.mpr ⟨hj, hh⟩
  have hone : ∀ i ∈ R, ∀ i' ∈ R, (spec.core.tail i = v ∨ spec.core.head i = v) →
      (spec.core.tail i' = v ∨ spec.core.head i' = v) → i = i' := by
    intro i hi i' hi' h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · by_contra hne
      have hlt := Finset.one_lt_card.mpr ⟨i, hmemA i hi h, i', hmemA i' hi' h', hne⟩
      omega
    · exfalso
      have h1 := Finset.card_pos.mpr ⟨i, hmemA i hi h⟩
      have h2 := Finset.card_pos.mpr ⟨i', hmemB i' hi' h'⟩
      omega
    · exfalso
      have h1 := Finset.card_pos.mpr ⟨i', hmemA i' hi' h'⟩
      have h2 := Finset.card_pos.mpr ⟨i, hmemB i hi h⟩
      omega
    · by_contra hne
      have hlt := Finset.one_lt_card.mpr ⟨i, hmemB i hi h, i', hmemB i' hi' h', hne⟩
      omega
  obtain ⟨leaf, hLeafR, hLeafEnd⟩ :
      ∃ leaf ∈ R, spec.core.tail leaf = v ∨ spec.core.head leaf = v := by
    rcases Nat.eq_zero_or_pos (R.filter fun e ↦ spec.core.tail e = v).card with h0 | hpos
    · have hpos2 : 0 < (R.filter fun e ↦ spec.core.head e = v).card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos2
      exact ⟨i, (Finset.mem_filter.mp hi).1, Or.inr (Finset.mem_filter.mp hi).2⟩
    · obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      exact ⟨i, (Finset.mem_filter.mp hi).1, Or.inl (Finset.mem_filter.mp hi).2⟩
  have hsimple : (spec.core.tail leaf = v ∧ spec.core.head leaf ≠ v) ∨
      (spec.core.head leaf = v ∧ spec.core.tail leaf ≠ v) := by
    rcases hLeafEnd with h | h
    · refine Or.inl ⟨h, fun hh ↦ ?_⟩
      have h1 := Finset.card_pos.mpr ⟨leaf, hmemA leaf hLeafR h⟩
      have h2 := Finset.card_pos.mpr ⟨leaf, hmemB leaf hLeafR hh⟩
      omega
    · refine Or.inr ⟨h, fun hh ↦ ?_⟩
      have h1 := Finset.card_pos.mpr ⟨leaf, hmemA leaf hLeafR hh⟩
      have h2 := Finset.card_pos.mpr ⟨leaf, hmemB leaf hLeafR h⟩
      omega
  obtain ⟨endEdge, hEndMem, hEndInc⟩ :
      ∃ edge ∈ strong.toPresentation.path (iface.slot leaf),
        Incident candidate.datum edge (dict.vertexAt v) := by
    rcases hLeafEnd with h | h
    · obtain ⟨edge, hedge⟩ := exists_head strong (iface.slot leaf)
      refine ⟨edge, List.mem_of_mem_head? (by rw [hedge]; rfl), ?_⟩
      have hplace : dict.vertexAt v = strong.start (iface.slot leaf) := by
        rw [← h]; exact dict.tail_eq leaf
      rw [hplace]
      exact (strong.head_isPathEnd (iface.slot leaf) edge (by rw [hedge]; rfl)).1
    · obtain ⟨edge, hedge⟩ := exists_getLast strong (iface.slot leaf)
      refine ⟨edge, List.mem_of_mem_getLast? (by rw [hedge]; rfl), ?_⟩
      have hplace : dict.vertexAt v = strong.finish (iface.slot leaf) := by
        rw [← h]; exact dict.head_eq leaf
      rw [hplace]
      exact (strong.getLast_isPathEnd (iface.slot leaf) edge (by rw [hedge]; rfl)).1
  have hEndC : slotOf candidate.datum face.realization endEdge ∈ C :=
    hRowSub leaf hLeafR endEdge hEndMem
  set label := (sourceVertexEquiv candidate.datum).symm (dict.vertexAt v) with hlabel
  have hVertex : sourceVertexOf candidate.datum label = dict.vertexAt v := by
    rw [hlabel, ← sourceVertexEquiv_apply, Equiv.apply_symm_apply]
  have hSlotAt : SlotAt (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      (slotOf candidate.datum face.realization endEdge) label := by
    rw [slotAt_iff_incident candidate.datum face.realization, sourceEdgeAt_slotOf, hVertex]
    exact hEndInc
  obtain ⟨other, hOtherC, hOtherNe, hOtherAt⟩ :=
    exists_ne_slotAt_of_minimal _ hNot hMin (core_loopless candidate.datum) hEndC hSlotAt
  rw [slotAt_iff_incident candidate.datum face.realization, hVertex] at hOtherAt
  obtain ⟨row₁, hrow₁⟩ := strong.decomposes.surviving_mem
    (face.realization.sourceEdgeAt other) (hSurvive other hOtherC)
  have hrow₁' : face.realization.sourceEdgeAt other
      ∈ strong.toPresentation.path (iface.slot (iface.slot.symm row₁)) := by
    rw [Equiv.apply_symm_apply]; exact hrow₁
  have hi₁R : iface.slot.symm row₁ ∈ R :=
    (hRmem _).mpr ⟨_, hrow₁', by rw [slotOf_sourceEdgeAt]; exact hOtherC⟩
  have hi₁v := end_of_incident dict hFaithful hSpanning hRows hrow₁' hOtherAt
  have hEq : iface.slot.symm row₁ = leaf := hone _ hi₁R _ hLeafR hi₁v hLeafEnd
  have hSame : face.realization.sourceEdgeAt other = endEdge :=
    unique_at_simple_end dict hFaithful hSpanning hRows hsimple (hEq ▸ hrow₁') hEndMem
      hOtherAt hEndInc
  exact hOtherNe (by
    rw [← slotOf_sourceEdgeAt candidate.datum face.realization other, hSame])

end Transfer

end Source

/-! ## 4.  The `SourceContractionTopology` producer at a general forest, and
the pencil transport

`TerminalGluing.sourceContractionTopology` already assembles the two fields of
`Candidate.ClearedFace.SourceContractionTopology` from the census forest and
the two target hypotheses the contracted gluing needs anyway; §3
supplies the census forest at a general expansion forest, and §2 supplies its
input.  The composite is exactly the `topology` argument that
`RetainedIndexProducer.terminalRetainedInputRefinement` and
`exists_subdivisionPencil_of_transport` consume. -/

section Producer

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.RequestedExpandedEndpoints
open DraismaVargas.LocalCases.RetainedIndexProducer
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TraversalPresentation
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

variable {tgt : CFGraph.{0}} {degree : ℕ} {data : GluingDatum tgt degree}
  {wall : tgt.V} {candidate : Candidate tgt degree data wall}
  {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ} {spec : Spec n p} {F : Finset (Fin p)}

/-- **The topology, produced at a general expansion forest.**  Its `forest`
field is §3 and its `notLoopy` field is `TerminalGluing.not_isLoopy_sourceZeroSet`,
which reads the target alone -- this is why the zero contraction is run on the
*source*, and not on `D.bigCore`, where `notLoopy` genuinely fails at a marker
carrying a loop (§2's `NoLoopDouble`). -/
theorem sourceContractionTopology_of_forest
    (strong : StrongPresentation candidate.datum coordinate)
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (dict : CoreDictionary spec strong iface)
    (hFaithful : Faithful dict) (hSpanning : Spanning dict)
    (hRows : RowsMeetEndsOnly strong)
    (hForest : IsForest spec.core F)
    (hConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0) :
    ClearedFace.SourceContractionTopology face :=
  DraismaVargas.LocalCases.TerminalGluing.sourceContractionTopology face
    (isForest_sourceZeroSet_of_forest strong iface face dict hFaithful hSpanning
      hRows hForest)
    hConnected hGenus

variable {chart : Type} {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}
  {N Q : ℕ} {D : ExpansionData n p N Q} {spec₀ : Spec n p}

/-- **An expansion datum plus a cleared terminal face gives the topology.**
Every hypothesis is explicit: the Euler count of §2, the dictionary hypotheses of
`StrongRefinement`, §3's `RowsMeetEndsOnly`, and the two target facts. -/
theorem sourceContractionTopology_of_expansion
    (hCond : D.Conditions spec₀.core) (hEuler : N + p = Q + n)
    (hN : 0 < N) (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix state.label)
    (slot : Fin Q ≃ coordinate)
    (hBase : baseFinish =
      expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot)
    (face : ClearedFace candidate strong.toPresentation state.currentFinish)
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong
      (terminalExpandedModelInterface hN hL state strong hStrongMatrix slot hBase))
    (hFaithful : Faithful dict) (hSpanning : Spanning dict)
    (hRows : RowsMeetEndsOnly strong)
    (hConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0) :
    ClearedFace.SourceContractionTopology face :=
  sourceContractionTopology_of_forest strong
    (terminalExpandedModelInterface hN hL state strong hStrongMatrix slot hBase)
    face dict hFaithful hSpanning hRows (isForest_expansionForest hCond hEuler)
    hConnected hGenus

/-- **The subdivision-pencil transport with `topology` discharged.**  The only
difference from `RetainedIndexProducer.exists_subdivisionPencil_of_transport`
is that the `SourceContractionTopology` is not assumed: it is produced from the
expansion datum, the Euler count and the source-side hypotheses. -/
theorem exists_subdivisionPencil_of_transport_of_expansion
    {n₁ p₁ : ℕ} {request : Spec n₁ p₁}
    (hbn : ∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
      BNExists (spec₀.scale k hk).graph r d ↔ BNExists (request.scale k hk).graph r d)
    (hCond : D.Conditions spec₀.core) (hEuler : N + p = Q + n)
    (hN : 0 < N) (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix state.label)
    (slot : Fin Q ≃ coordinate)
    (hBase : baseFinish =
      expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot)
    (face : ClearedFace candidate strong.toPresentation state.currentFinish)
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong
      (terminalExpandedModelInterface hN hL state strong hStrongMatrix slot hBase))
    (hFaithful : Faithful dict) (hSpanning : Spanning dict)
    (hRows : RowsMeetEndsOnly strong)
    (hTargetConnected : graph_connected (TargetExpansion.graph tgt wall candidate.right))
    (hTargetGenus : genus (TargetExpansion.graph tgt wall candidate.right) = 0)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses
      (sourceContractionTopology_of_expansion hCond hEuler hN hL state strong
        hStrongMatrix slot hBase face dict hFaithful hSpanning hRows
        hTargetConnected hTargetGenus)).Nonempty)
    (relabeling : LaplacianEquiv
      (terminalRetainedRefinedSpec hCond hN hL state strong hStrongMatrix slot
        hBase face).graph
      (ClearedFace.SourceContractionTopology.prunedSpec
        (sourceContractionTopology_of_expansion hCond hEuler hN hL state strong
          hStrongMatrix slot hBase face dict hFaithful hSpanning hRows
          hTargetConnected hTargetGenus) hKept).graph)
    (contracted : ClearedFace.ContractedGluing
      (sourceContractionTopology_of_expansion hCond hEuler hN hL state strong
        hStrongMatrix slot hBase face dict hFaithful hSpanning hRows
        hTargetConnected hTargetGenus))
    (hSourceConnected : candidate.datum.Connected) :
    ∃ pencil : DraismaVargas.SubdivisionPencil request degree,
      pencil.scale = face.scale :=
  exists_subdivisionPencil_of_transport hbn hCond hN hL state strong hStrongMatrix
    slot hBase hKept relabeling contracted hSourceConnected

/-! ### The Euler count holds for the datum of the stable-model reduction -/

/-- The stable-model reduction produces a cubic model with `N = 2(p - n)`
vertices and `Q = 3(p - n)`
slots, so the Euler count `N + p = Q + n` of §2 is arithmetic there. -/
theorem euler_of_cubicShape {n₀ p₀ : ℕ} (h : n₀ ≤ p₀) :
    2 * (p₀ - n₀) + p₀ = 3 * (p₀ - n₀) + n₀ := by omega

/-- **The datum half, unconditionally, on the output of the stable-model
reduction.**  Every clause of
`RetainedIndexProducer.exists_expansionModel_retainedIndex`, plus the datum
half: the expansion forest of the produced datum *is* a census forest of the
cubic core.  No Euler hypothesis remains: the shape of the reduction's output
supplies it. -/
theorem exists_expansionModel_isForest {n₁ p₁ : ℕ} (request : Spec n₁ p₁)
    (hConn : request.core.Connected) (hGenus : n₁ < p₁) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀)))
      (hN : 0 < 2 * (p₀ - n₀))
      (hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e),
      D.Conditions spec₀.core ∧
        IsForest D.bigCore (expansionForest D) ∧
        Nonempty (RetainedIndex (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀) ∧
        (∀ (d k : ℕ) (hk : 0 < k), BNExists (spec₀.scale k hk).graph 1 (d : ℤ) →
          ∃ pencil : DraismaVargas.SubdivisionPencil request d, pencil.scale = k) := by
  obtain ⟨n₀, p₀, spec₀, D, hN, hL, hCond, -, -, hg₀, hRet, hbn⟩ :=
    exists_expansionModel_retainedIndex request hConn hGenus
  refine ⟨n₀, p₀, spec₀, D, hN, hL, hCond, ?_, hRet, hbn⟩
  have hle : n₀ ≤ p₀ := by
    have : (n₀ : ℤ) < p₀ := by
      have : (n₁ : ℤ) < p₁ := by exact_mod_cast hGenus
      omega
    exact_mod_cast this.le
  exact isForest_expansionForest hCond (euler_of_cubicShape hle)

end Producer

/-! ## 5.  Why `RowsMeetEndsOnly` holds

The hypothesis `RowsMeetEndsOnly` of §3 is derived in the module
`RowsMeetEndsOnly`:
`rowsMeetEndsOnly_of_strong : (∀ row, strong.start row ≠ strong.finish row) →
RowsMeetEndsOnly strong`, and §3's and §4's theorems are restated there without
it.  It is **not** a new kind of assumption: it is the statement that a
displayed row is a *maximal* stable path in the strongest occurrence-level
sense, the same content `StrongPresentation.head_isPathEnd` and
`getLast_isPathEnd` assert at the two ends only.  Here is the case analysis.

Fix a row, an occurrence `edge` of it and a vertex `u` with
`Incident data edge u` and `nonDanglingValency data u ≠ 2`.  `Incident` is
membership in the *two* entries of `data.sourceEnds edge`, so `u` is one of
them, and the argument is a case split on the position of `edge` in
`strong.toPresentation.path row`:

* `edge` is the **first** occurrence of a row of length `≥ 2`.  `chain` gives
  the vertex `m` where it meets the second occurrence, with
  `nonDanglingValency data m = 2`; `head_isPathEnd` gives
  `Incident data edge (strong.start row)`.  Since `u ≠ m` (their valencies
  differ) and `edge` has only two ends, `u = strong.start row`.
* `edge` is the **last** occurrence: symmetric, through `getLast_isPathEnd`.
* `edge` is an **interior** occurrence.  Let `m₁`, `m₂` be the vertices where
  it meets its predecessor and its successor; both have surviving valency two.
  If `m₁ = m₂`, then the predecessor, `edge` and the successor -- three
  *distinct* occurrences, by `Decomposes.nodup` -- are surviving and incident
  at a valency-two vertex, contradicting
  `W4StableSource.nonDanglingIncident_eq_pair`.  So `m₁ ≠ m₂`, the two ends of
  `edge` are exactly `m₁` and `m₂`, and no `u` of valency `≠ 2` is incident at
  all.
* the row has **length one**.  Then `edge` sits at both `strong.start row` and
  `strong.finish row`, which are distinct by `start_ne_finish` (§3, from
  `Spec.core_loopless` through `Faithful`), so again `u` is one of them.

The interior case also needs one step of list combinatorics, because of the
shape of `chain`: `StrongPresentation.chain` is a `List.IsChain (MeetsAt data)`
on `strong.toPresentation.path row`, which exposes *consecutive pairs* and not
*positions*.  Turning "`edge` is a member that is neither the head nor the
last" into "`edge` has a predecessor and a successor in the chain" needs the
list-splitting step

```
edge ∈ l → l.head? ≠ some edge → l.getLast? ≠ some edge →
  ∃ prefix a b suffix, l = prefix ++ a :: edge :: b :: suffix
```

together with the transport of `List.IsChain` to the two adjacent pairs of
that decomposition.  The module `RowsMeetEndsOnly` proves both.

The other three hypotheses of the module docstring are *not* of this kind:
`Faithful` cannot be derived, by `StrongRefinement` §3-§4, the core dictionary
is an input, and the Euler count of §2 is genus preservation, which
`ExpansionData.Conditions` does not imply (a fibre carrying a cycle satisfies
every clause of `Conditions`) -- though `exists_expansionModel_isForest` shows
that the output of the stable-model reduction supplies it by arithmetic, so §2
is unconditional where it is actually used.
-/

end DraismaVargas.LocalCases.ForestReceiptGeneral
