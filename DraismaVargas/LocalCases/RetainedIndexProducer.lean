import DraismaVargas.LocalCases.RequestedExpandedEndpoints

/-!
# The `RetainedIndex` producer from the requested expansion datum

**Source.**  Draisma–Vargas Part I, arXiv:1909.12924, the proof of the main result (subsection
`section-proof-main-result`): a non-trivalent requested type is presented as a
point of the *closed* cone of a trivalent one, with zero length on the
collapsed edges.  The exact integral-scale transport used here has no verbatim
counterpart in the paper, so everything below is original formalization adapted
from that closed-cone presentation and from nothing else; the paper never
indexes retained cubic slots by requested slots, and the marker analysis of §2
is not in the source.

## What is proved

`InputRefinementData.RetainedIndex spec F small` is the interface through which
`InputRefinementData.Retained.inputRefinement` re-bases a cleared face's
refinement on the slots outside the expansion forest.  This file produces one,
**unconditionally**, from `RequestedExpandedEndpoints.exists_expansionModel`'s
datum `D : ExpansionData n p N Q`.

1. **The producer** (§3).  `retainedIndex` builds
   `RetainedIndex (D.bigSpec small hN hL) (expansionForest D) small` with the
   carrier list read off `CoreExpansion.SlotKind`: a retained cubic slot of
   kind `.single j` carries `[j]`, one of kind `.double j₁ j₂` carries
   `[j₁, j₂]` in the order recorded by `ExpansionData.side`, and the
   contracted kinds are excluded by the retained-slot hypothesis.  `owner` is
   `ExpansionData.owner`, `pos` is `side`.  No hypothesis beyond
   `D.Conditions small.core` and the expansion model's own `hN`, `hL`.

2. **Why the interface carries lists** (§2), and it is a theorem, not a
   caveat.  `owner` is *always* onto the retained slots
   (`ownerRetained_surjective`), but it is injective only in the absence of
   `SlotKind.double` slots: a `double` slot carries **two** requested slots in
   series through a marker.  `markerFree_of_equiv` proves the converse — any
   equivalence `Fin p ≃ {e // e ∉ expansionForest D}` forces `MarkerFree D` —
   so an interface asking for one retained slot per requested slot is available
   exactly on marker-free data, which is what `markerFree_of_retainedIndex`
   records (a carrier assignment by singletons *is* such an equivalence).
   `card_retained_lt_of_double` quantifies the mismatch: one `double` already
   makes the retained cubic slots strictly fewer than the requested slots.
   `markerFree_iff_fib_surjective` reads the condition off the geometry — no
   `double` if and only if the fibre map `D.fib` is onto the requested core,
   the vertices it misses being exactly the markers
   (`ExpansionData.MarkerIsolated`), the bivalent vertices by which the reduced
   core of the expansion model displays a loop of the underlying metric graph
   looplessly — and `markerFree_iff_side` reads it off the datum's own
   bookkeeping.  `not_markerFree_of_card_lt` and
   `exists_conditions_not_markerFree` show the marker case really occurs:
   `StableModelReduction.wedge_expansion`, the expansion model of the wedge of
   two loops, has `p = 4` requested slots over `Q = 3` cubic slots.
   `retainedIndex_markerFree` is the special case: on marker-free data every
   carrier list is a singleton, which is an equivalence.

3. **The terminal composite** (§5), with no marker hypothesis.  At a cleared
   face of the expanded model whose interface is
   `RequestedExpandedEndpoints.terminalForestInterface`, the producer and
   `Retained.inputRefinement` deliver a `ClearedFace.InputRefinement` of the
   **requested** specification `spec₀` scaled by the face's own scale, hence —
   with a contracted gluing datum — a `SubdivisionPencil spec₀ degree` at
   exactly that scale, and through the expansion model's two-way scale-wise
   transport a `SubdivisionPencil` of the original arbitrary connected request.

## The hypotheses that remain explicit

* The `SourceContractionTopology` itself.  At a nonempty forest the zero set of
  the face contains whole rows, and `CycleRows.isForest_sourceZeroSet` is
  stated at the empty forest; the general-`F` forest statement is taken here
  as the hypothesis `topology`, together with `hKept`.  Both are produced in
  `StatementFromLink`: `topology` by
  `RowsMeetEndsOnly.sourceContractionTopology_of_forest` (via
  `ForestReceiptGeneral.sourceContractionTopology_of_forest`), and `hKept`
  from `Spanning` alone.
* The `LaplacianEquiv` onto the pruned contracted source, which is
  `Retained.inputRefinement`'s own remaining input and stays a hypothesis here.
  Cutting a source occurrence at a marker does not weaken it: the unit
  subdivision does not see an extra core vertex at an interior integer point
  (`Infrastructure.OrderedBlockSplit`).
* The `ContractedGluing` datum and `candidate.datum.Connected`.  Both are
  produced in `StatementFromLink`: `ContractedGluing` by
  `TerminalGluing.contractedGluing_of_incoming` (no interface and no forest
  needed), and connectedness from `data.Valid` alone.
* Reaching such a terminal face at all, which is the business of the march and
  the outer walk: the march state, its strong presentation and `hStrongMatrix`
  are hypotheses.

## How the pieces of the transport fit

Dropping the forest rows and re-basing the refinement on the retained slots,
and splitting a `double` row's occurrence list at its marker, are `retainedIndex`
above together with `InputRefinementData.Retained.blockSegments`; the
general-`F` forest statement is the `topology` hypothesis of §5; the rank
transport at the terminal face, the transport back to the request, and the
cardinality read against the cubic model rather than the request are exhibited
by `exists_subdivisionPencil_requested` and
`exists_subdivisionPencil_of_transport` through the `ClosedEndpoint` chain, the
interface being taken at `D.bigSpec` (where `2 Q = 3 N`) and the refinement
target at `spec₀`.

## Consumers

The transport to the requested graph: `ForestReceiptGeneral`, and
`RetainedRelabeling`, whose producer runs at `retainedIndex`; the terminal
identification `TerminalIdentification.carriesCertifiedPencil_of_tracked_expanded`
is stated in the shape `exists_subdivisionPencil_of_transport` takes.

## Non-vacuity

`bananaRetainedIndex` runs the producer on `RequestedExpandedEndpoints`'
four-fold banana — a **nonempty** two-slot expansion forest — and
`bananaRetainedIndex_eq` proves it *is* the hand-built
`RequestedExpandedEndpoints.bananaRetained`.  `MarkerFree` itself is inhabited
there (`banana_markerFree`, by evaluation) and fails at the wedge.
-/

namespace DraismaVargas.LocalCases.RetainedIndexProducer

open Utilities
open Utilities.Certificate
open Utilities.Certificate.IteratedSplitRefinement
open Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion
open ExplicitPotential
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.RequestedExpandedEndpoints

/-! ## 1.  Marker-free expansion data -/

section Free

variable {n p N Q : ℕ}

/-- **The datum has no `double` slot.**  A `SlotKind.double j₁ j₂` slot of the
cubic model carries the two requested slots `j₁`, `j₂` in series through a
marker — the bivalent vertex by which a *loop* of the requested metric graph is
displayed looplessly — so it is owned by two requested slots at once.  This
predicate says that never happens. -/
def MarkerFree (D : ExpansionData n p N Q) : Prop :=
  ∀ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e ≠ SlotKind.double j₁ j₂

instance decidableMarkerFree (D : ExpansionData n p N Q) : Decidable (MarkerFree D) := by
  unfold MarkerFree; infer_instance

variable {D : ExpansionData n p N Q} {C : Core n p}

/-- On a marker-free datum every requested slot is carried by its owner as a
`single`. -/
theorem kind_owner (hCond : D.Conditions C) (hMF : MarkerFree D) (j : Fin p) :
    D.kind (D.owner j) = SlotKind.single j := by
  rcases ExpansionData.exists_carrier hCond j with ⟨hk, -⟩ | ⟨j₂, hk, -⟩ | ⟨j₁, hk, -⟩
  · exact hk
  · exact absurd hk (hMF _ _ _)
  · exact absurd hk (hMF _ _ _)

/-- The owner map, with values in the retained slots.  `owner_not_mem_expansionForest`
is the proof that an owner is never contracted. -/
def ownerRetained (hCond : D.Conditions C) (j : Fin p) :
    {e : Fin Q // e ∉ expansionForest D} :=
  ⟨D.owner j, owner_not_mem_expansionForest hCond j⟩

@[simp] theorem ownerRetained_val (hCond : D.Conditions C) (j : Fin p) :
    (ownerRetained hCond j : Fin Q) = D.owner j := rfl

/-- **Always onto.**  Every retained cubic slot is a `single` or a `double`, and
in either case it is the owner of a requested slot. -/
theorem ownerRetained_surjective (hCond : D.Conditions C) :
    Function.Surjective (ownerRetained hCond) := by
  rintro ⟨e, he⟩
  have hk : D.kind e ≠ SlotKind.contracted := by
    simpa only [mem_expansionForest] using he
  cases hkind : D.kind e with
  | contracted => exact absurd hkind hk
  | single j => exact ⟨j, Subtype.ext (ExpansionData.owner_eq_of_single hCond hkind).1⟩
  | double j₁ j₂ => exact ⟨j₁, Subtype.ext (ExpansionData.owner_eq_of_double hCond hkind).1⟩

/-- **Injective exactly when marker-free.** -/
theorem ownerRetained_injective (hCond : D.Conditions C) (hMF : MarkerFree D) :
    Function.Injective (ownerRetained hCond) := by
  intro j j' h
  have h1 := kind_owner hCond hMF j
  have h2 := kind_owner hCond hMF j'
  have hown : D.owner j = D.owner j' := congrArg Subtype.val h
  rw [hown, h2] at h1
  simpa using h1.symm

theorem ownerRetained_bijective (hCond : D.Conditions C) (hMF : MarkerFree D) :
    Function.Bijective (ownerRetained hCond) :=
  ⟨ownerRetained_injective hCond hMF, ownerRetained_surjective hCond⟩

/-- The slot equivalence available on marker-free data: requested slots are the
retained cubic slots, one for one. -/
noncomputable def retainedSlotEquiv (hCond : D.Conditions C) (hMF : MarkerFree D) :
    Fin p ≃ {e : Fin Q // e ∉ expansionForest D} :=
  Equiv.ofBijective (ownerRetained hCond) (ownerRetained_bijective hCond hMF)

@[simp] theorem retainedSlotEquiv_val (hCond : D.Conditions C) (hMF : MarkerFree D)
    (j : Fin p) : ((retainedSlotEquiv hCond hMF j : {e : Fin Q // e ∉ expansionForest D}) :
      Fin Q) = D.owner j := rfl

/-- Marker-freeness read off the datum's own bookkeeping: no requested slot is
the *second* half of a `double`. -/
theorem markerFree_iff_side (hCond : D.Conditions C) :
    MarkerFree D ↔ ∀ j : Fin p, D.side j = false := by
  constructor
  · intro hMF j
    rcases ExpansionData.exists_carrier hCond j with ⟨-, hs⟩ | ⟨j₂, hk, -⟩ | ⟨j₁, hk, -⟩
    · exact hs
    · exact absurd hk (hMF _ _ _)
    · exact absurd hk (hMF _ _ _)
  · intro hside e j₁ j₂ hk
    obtain ⟨-, -, -, hs2⟩ := ExpansionData.owner_eq_of_double hCond hk
    rw [hside j₂] at hs2
    exact Bool.noConfusion hs2

end Free

/-! ## 2.  Why the interface carries lists

An interface asking for **one** retained slot per requested slot is broken by a
`double` slot, and §2 shows the break is an equivalence, so
`InputRefinementData.RetainedIndex` has to assign ordered carrier lists. -/

section Obstruction

variable {n p N Q : ℕ} {D : ExpansionData n p N Q} {C : Core n p}

/-- **One slot per requested slot forces marker-freeness.**  If the requested slots are in
bijection with the retained cubic slots at all, then no cubic slot carries two
requested slots.  `owner` is always onto the retained slots, so equal
cardinalities make it injective, and the two halves of a `double` have
different `side` flags. -/
theorem markerFree_of_equiv (hCond : D.Conditions C)
    (E : Fin p ≃ {e : Fin Q // e ∉ expansionForest D}) : MarkerFree D := by
  have hcard : Fintype.card (Fin p) = Fintype.card {e : Fin Q // e ∉ expansionForest D} :=
    Fintype.card_congr E
  have hbij : Function.Bijective (ownerRetained hCond) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr ⟨ownerRetained_surjective hCond, hcard⟩
  intro e j₁ j₂ hk
  obtain ⟨h1, hs1, h2, hs2⟩ := ExpansionData.owner_eq_of_double hCond hk
  have : ownerRetained hCond j₁ = ownerRetained hCond j₂ :=
    Subtype.ext (by rw [ownerRetained_val, ownerRetained_val, h1, h2])
  have hj : j₁ = j₂ := hbij.1 this
  rw [hj, hs2] at hs1
  exact Bool.noConfusion hs1

/-- **The gate, stated at the widened `RetainedIndex`.**  A retained indexing
all of whose carrier lists are singletons *is* the pre-widening equivalence, and
therefore exists only on marker-free data. -/
theorem markerFree_of_retainedIndex {small : Spec n p} (hCond : D.Conditions small.core)
    (hN : 0 < N) (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (idx : RetainedIndex (D.bigSpec small hN hL) (expansionForest D) small)
    (hsingle : ∀ e : {e : Fin Q // e ∉ expansionForest D},
      ∃ j : Fin p, idx.carried e = [j]) :
    MarkerFree D := by
  have hhead : ∀ (l : List (Fin p)) (a : Fin p) (h : l = [a]) (hne : l ≠ []),
      l.head hne = a := by
    rintro l a rfl hne
    rfl
  have hmem : ∀ e, (idx.carried e).head (idx.carried_ne_nil e) ∈ idx.carried e :=
    fun e ↦ List.head_mem _
  have hown : ∀ e, idx.owner ((idx.carried e).head (idx.carried_ne_nil e)) = e :=
    fun e ↦ idx.owner_eq_of_mem e _ (hmem e)
  have hbij :
      Function.Bijective (fun e ↦ (idx.carried e).head (idx.carried_ne_nil e)) := by
    constructor
    · intro e e' h
      rw [← hown e, ← hown e']
      exact congrArg idx.owner h
    · intro j
      refine ⟨idx.owner j, ?_⟩
      obtain ⟨j', hj'⟩ := hsingle (idx.owner j)
      have hj := idx.mem_carried_owner j
      rw [hj'] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      show (idx.carried (idx.owner j)).head (idx.carried_ne_nil (idx.owner j)) = j
      rw [hhead _ j' hj' (idx.carried_ne_nil (idx.owner j))]
      exact hj.symm
  exact markerFree_of_equiv hCond (Equiv.ofBijective _ hbij).symm

/-- **Marker-freeness is a property of the fibre map.**  A `double` slot exists
exactly when some requested core vertex is missed by `D.fib` — that vertex is
the marker, and `ExpansionData.MarkerIsolated` is precisely the statement that
it is outside the image. -/
theorem markerFree_iff_fib_surjective (hCond : D.Conditions C) :
    MarkerFree D ↔ Function.Surjective D.fib := by
  constructor
  · intro hMF w
    obtain ⟨j, hj⟩ := ExpansionData.incident_of_conditions hCond w
    have hk := kind_owner hCond hMF j
    obtain ⟨-, hsingle, -⟩ := ExpansionData.compatible_of_conditions hCond (D.owner j)
    obtain ⟨ht, hh⟩ := hsingle j hk
    rcases hj with hj | hj
    · exact ⟨D.bigCore.tail (D.owner j), by rw [ht, hj]⟩
    · exact ⟨D.bigCore.head (D.owner j), by rw [hh, hj]⟩
  · intro hsurj e j₁ j₂ hk
    obtain ⟨hout, -⟩ := ExpansionData.marker_of_conditions hCond e j₁ j₂ hk
    obtain ⟨v, hv⟩ := hsurj (C.head j₁)
    exact hout v hv

/-- **A counting obstruction.**  More requested slots than cubic slots is
already incompatible with marker-freeness. -/
theorem not_markerFree_of_card_lt (hCond : D.Conditions C) (hlt : Q < p) :
    ¬ MarkerFree D := by
  intro hMF
  have hcard := Fintype.card_of_bijective (ownerRetained_bijective hCond hMF)
  have hle : Fintype.card {e : Fin Q // e ∉ expansionForest D} ≤ Fintype.card (Fin Q) :=
    Fintype.card_subtype_le _
  rw [Fintype.card_fin] at hcard hle
  omega

/-- **The mismatch, quantified.**  As soon as one cubic slot is a `double`, the
cubic model has strictly fewer retained slots than the request has slots, so no
interface asking for one retained slot per requested slot (an equivalence
`Fin p ≃ {e // e ∉ expansionForest D}`) can be satisfied. -/
theorem card_retained_lt_of_double (hCond : D.Conditions C) {e : Fin Q} {j₁ j₂ : Fin p}
    (hk : D.kind e = SlotKind.double j₁ j₂) :
    Fintype.card {e : Fin Q // e ∉ expansionForest D} < p := by
  have hle : Fintype.card {e : Fin Q // e ∉ expansionForest D} ≤ Fintype.card (Fin p) :=
    Fintype.card_le_of_surjective _ (ownerRetained_surjective hCond)
  rw [Fintype.card_fin] at hle
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd hk (markerFree_of_equiv hCond
      (Fintype.equivOfCardEq (by rw [Fintype.card_fin, h])) e j₁ j₂)

end Obstruction

/-! ## 3.  The producer -/

section Producer

variable {n p N Q : ℕ} {D : ExpansionData n p N Q} {C : Core n p} {small : Spec n p}

/-- The requested slots a cubic slot carries, in series order, by its role. -/
def kindCarried : SlotKind p → List (Fin p)
  | SlotKind.contracted => []
  | SlotKind.single j => [j]
  | SlotKind.double j₁ j₂ => [j₁, j₂]

@[simp] theorem kindCarried_single (j : Fin p) :
    kindCarried (SlotKind.single j) = [j] := rfl

@[simp] theorem kindCarried_double (j₁ j₂ : Fin p) :
    kindCarried (SlotKind.double j₁ j₂) = [j₁, j₂] := rfl

/-- The lengths along a retained slot add up to its `CoreExpansion` length. -/
theorem sum_map_kindCarried (small : Spec n p) {k : SlotKind p}
    (hk : k ≠ SlotKind.contracted) :
    ((kindCarried k).map small.length).sum = kindLength small k := by
  cases k with
  | contracted => exact absurd rfl hk
  | single j => simp [kindCarried, kindLength]
  | double j₁ j₂ => simp [kindCarried, kindLength]

/-- **The `RetainedIndex` producer, unconditionally.**  A retained cubic slot
carries the requested slots its `CoreExpansion.SlotKind` names, in the order
`ExpansionData.side` records, and their lengths add up to its own.

It drops the forest rows and re-bases the refinement on the retained slots,
splitting a `double` row's occurrence list at its marker.  Its only hypotheses
are outputs of `RequestedExpandedEndpoints.exists_expansionModel`. -/
def retainedIndex (hCond : D.Conditions small.core)
    (hN : 0 < N) (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) :
    RetainedIndex (D.bigSpec small hN hL) (expansionForest D) small where
  carried := fun e ↦ kindCarried (D.kind ↑e)
  owner := fun j ↦ ownerRetained hCond j
  pos := fun j ↦ if D.side j then 1 else 0
  carried_getElem := by
    intro j
    rcases ExpansionData.exists_carrier hCond j with ⟨hk, hs⟩ | ⟨j₂, hk, hs⟩ | ⟨j₁, hk, hs⟩ <;>
      simp only [ownerRetained_val, hk, hs, kindCarried] <;> rfl
  owner_eq_of_mem := by
    rintro ⟨e, he⟩ j hj
    refine Subtype.ext ?_
    simp only [ownerRetained_val]
    cases hkind : D.kind e with
    | contracted =>
        rw [hkind] at hj
        simp [kindCarried] at hj
    | single j' =>
        rw [hkind] at hj
        simp only [kindCarried, List.mem_cons, List.not_mem_nil, or_false] at hj
        subst hj
        exact (ExpansionData.owner_eq_of_single hCond hkind).1
    | double j₁ j₂ =>
        rw [hkind] at hj
        obtain ⟨h1, -, h2, -⟩ := ExpansionData.owner_eq_of_double hCond hkind
        simp only [kindCarried, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with hj | hj
        · subst hj; exact h1
        · subst hj; exact h2
  nodup := by
    rintro ⟨e, he⟩
    cases hkind : D.kind e with
    | contracted => simp [kindCarried]
    | single j => simp [kindCarried]
    | double j₁ j₂ =>
        obtain ⟨-, hs1, -, hs2⟩ := ExpansionData.owner_eq_of_double hCond hkind
        have hne : j₁ ≠ j₂ := by
          intro h
          rw [h, hs2] at hs1
          exact Bool.noConfusion hs1
        simp [kindCarried, hne]
  carried_ne_nil := by
    rintro ⟨e, he⟩
    have hk : D.kind e ≠ SlotKind.contracted := by
      simpa only [mem_expansionForest] using he
    cases hkind : D.kind e with
    | contracted => exact absurd hkind hk
    | single j => simp [kindCarried]
    | double j₁ j₂ => simp [kindCarried]
  length_eq := by
    rintro ⟨e, he⟩
    have hk : D.kind e ≠ SlotKind.contracted := by
      simpa only [mem_expansionForest] using he
    exact (sum_map_kindCarried small hk).symm

@[simp] theorem retainedIndex_owner_val (hCond : D.Conditions small.core)
    (hN : 0 < N) (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (j : Fin p) :
    (((retainedIndex hCond hN hL).owner j :
      {e : Fin Q // e ∉ expansionForest D}) : Fin Q) = D.owner j := rfl

@[simp] theorem retainedIndex_carried (hCond : D.Conditions small.core)
    (hN : 0 < N) (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (e : {e : Fin Q // e ∉ expansionForest D}) :
    (retainedIndex hCond hN hL).carried e = kindCarried (D.kind ↑e) := rfl

/-- **The marker-free special case.**  Every carrier list is a singleton, which
is exactly an equivalence between the requested slots and the retained slots;
`markerFree_of_retainedIndex` is the converse. -/
theorem retainedIndex_markerFree (hCond : D.Conditions small.core) (hMF : MarkerFree D)
    (hN : 0 < N) (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (e : {e : Fin Q // e ∉ expansionForest D}) :
    ∃ j : Fin p, (retainedIndex hCond hN hL).carried e = [j] := by
  obtain ⟨j, hj⟩ := ownerRetained_surjective hCond e
  refine ⟨j, ?_⟩
  rw [retainedIndex_carried, ← hj, ownerRetained_val, kind_owner hCond hMF j]
  rfl

end Producer

/-! ## 4.  Non-vacuity

The producer is run at `RequestedExpandedEndpoints`' four-fold banana, whose
expansion forest has two slots, and is checked against the hand-built
`bananaRetained`.  §4's last theorem shows the marker case is inhabited too, by
the wedge witness of the expansion model. -/

section Witness

theorem banana_markerFree : MarkerFree bananaExpansion := by decide

/-- The producer at a **nonempty** expansion forest. -/
def bananaRetainedIndex :
    RetainedIndex bananaBigSpec (expansionForest bananaExpansion) bananaSpec :=
  retainedIndex banana_conditions (by norm_num) banana_bigLoopless

theorem bananaRetainedIndex_owner (j : Fin 4) :
    ((bananaRetainedIndex.owner j :
      {e : Fin 6 // e ∉ expansionForest bananaExpansion}) : Fin 6) =
      bananaExpansion.owner j := rfl

/-- **The producer reproduces the hand-built witness**, on the nose. -/
theorem bananaRetainedIndex_eq : bananaRetainedIndex = bananaRetained := by
  have hc : bananaRetainedIndex.carried = bananaRetained.carried := by decide
  have ho : bananaRetainedIndex.owner = bananaRetained.owner := by decide
  have hp : bananaRetainedIndex.pos = bananaRetained.pos := by decide
  cases hi : bananaRetainedIndex
  cases hb : bananaRetained
  rw [hi, hb] at hc ho hp
  subst hc
  subst ho
  subst hp
  rfl

/-- **The marker case is inhabited.**  `StableModelReduction.wedge_expansion` is
the marker-aware expansion of the wedge of two loops: four requested
slots over a three-slot cubic model, so no *singleton* carrier assignment on it
exists and `Retained.blockSegments` really has to cut a row. -/
theorem exists_conditions_not_markerFree :
    ∃ D : ExpansionData 3 4 2 3,
      D.Conditions StableModelReduction.wedgeCore ∧ ¬ MarkerFree D := by
  obtain ⟨D, hCond, -, -⟩ := StableModelReduction.wedge_expansion
  exact ⟨D, hCond, not_markerFree_of_card_lt hCond (by norm_num)⟩

end Witness

/-! ## 5.  The terminal composite: an `InputRefinement` of the *requested* spec

`RequestedExpandedEndpoints.terminalForestInterface` hands a terminal march
state's interface at the expansion forest; §3's producer re-bases it on the
retained slots; `InputRefinementData.Retained.inputRefinement` then refines the
**requested** specification `spec₀` — not the cubic model — at the face's own
scale.  Everything the composite assumes is an explicit argument; the module
docstring lists them. -/

section Terminal

open DraismaVargas.LocalCases.TraversalPresentation

variable {coordinate chart : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {target : CFGraph} {gluing : GluingDatum target degree}
  {wall : target.V} {candidate : Candidate target degree gluing wall}
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}
  {n p N Q : ℕ} {D : ExpansionData n p N Q} {spec₀ : Spec n p}

/-- The terminal interface of the expanded model, at the expansion forest. -/
def terminalExpandedModelInterface (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix state.label)
    (slot : Fin Q ≃ coordinate)
    (hBase : baseFinish =
      expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot) :
    InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation state.currentFinish
      (expansionForest D) :=
  terminalForestInterface (expansionForest D) state strong hStrongMatrix slot hBase

/-- The canonical positive refinement of the **requested** specification cut out
by such a face: the segments of slot `j` are the cleared source occurrences
allotted to it along the row displaying the retained cubic slot `D.owner j`. -/
noncomputable def terminalRetainedRefinedSpec (hCond : D.Conditions spec₀.core)
    (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix state.label)
    (slot : Fin Q ≃ coordinate)
    (hBase : baseFinish =
      expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot)
    (face : ClearedFace candidate strong.toPresentation state.currentFinish) :
    PackedSpec :=
  Retained.refinedSpec
    (terminalExpandedModelInterface hN hL state strong hStrongMatrix slot hBase) face
    (retainedIndex hCond hN hL)

/-- **The headline, as data.**  From the expansion datum of
`RequestedExpandedEndpoints.exists_expansionModel`, a terminal march state
carrying the expanded endpoint vector, a cleared face of the expanded model and
the two remaining source-side inputs, a closed-face input refinement of the
**requested** specification.  No marker hypothesis. -/
noncomputable def terminalRetainedInputRefinement (hCond : D.Conditions spec₀.core)
    (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix state.label)
    (slot : Fin Q ≃ coordinate)
    (hBase : baseFinish =
      expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot)
    {face : ClearedFace candidate strong.toPresentation state.currentFinish}
    {topology : ClearedFace.SourceContractionTopology face}
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (relabeling : LaplacianEquiv
      (terminalRetainedRefinedSpec hCond hN hL state strong hStrongMatrix slot
        hBase face).graph
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).graph) :
    ClearedFace.InputRefinement spec₀ topology :=
  Retained.inputRefinement
    (terminalExpandedModelInterface hN hL state strong hStrongMatrix slot hBase)
    (retainedIndex hCond hN hL) hKept relabeling

/-- **The headline, as a pencil.**  With the contracted gluing datum
the same data give an actual `SubdivisionPencil` of the requested
specification, at exactly the face's common denominator-clearing scale. -/
theorem exists_subdivisionPencil_requested (hCond : D.Conditions spec₀.core)
    (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix state.label)
    (slot : Fin Q ≃ coordinate)
    (hBase : baseFinish =
      expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot)
    {face : ClearedFace candidate strong.toPresentation state.currentFinish}
    {topology : ClearedFace.SourceContractionTopology face}
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (relabeling : LaplacianEquiv
      (terminalRetainedRefinedSpec hCond hN hL state strong hStrongMatrix slot
        hBase face).graph
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).graph)
    (contracted : ClearedFace.ContractedGluing topology)
    (hConnected : candidate.datum.Connected) :
    ∃ pencil : DraismaVargas.SubdivisionPencil spec₀ degree, pencil.scale = face.scale :=
  ClearedFace.exists_subdivisionPencil contracted
    (terminalRetainedInputRefinement hCond hN hL state strong hStrongMatrix slot
      hBase hKept relabeling) hConnected

/-- **and transported back to the arbitrary connected request.**  The
scale-wise two-way Brill--Noether transport (`exists_expansionModel`'s last
clause) carries the pencil from the reduced representative `spec₀` to the
originally requested specification, at the same scale. -/
theorem exists_subdivisionPencil_of_transport {n₁ p₁ : ℕ} {spec : Spec n₁ p₁}
    (hbn : ∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
      BNExists (spec₀.scale k hk).graph r d ↔ BNExists (spec.scale k hk).graph r d)
    (hCond : D.Conditions spec₀.core)
    (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (state : FiniteAtlasMarch.State matrix baseStart baseFinish)
    (strong : StrongPresentation candidate.datum coordinate)
    (hStrongMatrix : GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
      matrix state.label)
    (slot : Fin Q ≃ coordinate)
    (hBase : baseFinish =
      expandedFinish (D.bigSpec spec₀ hN hL) (expansionForest D) slot)
    {face : ClearedFace candidate strong.toPresentation state.currentFinish}
    {topology : ClearedFace.SourceContractionTopology face}
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (relabeling : LaplacianEquiv
      (terminalRetainedRefinedSpec hCond hN hL state strong hStrongMatrix slot
        hBase face).graph
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept).graph)
    (contracted : ClearedFace.ContractedGluing topology)
    (hConnected : candidate.datum.Connected) :
    ∃ pencil : DraismaVargas.SubdivisionPencil spec degree, pencil.scale = face.scale := by
  obtain ⟨w, hw⟩ := exists_subdivisionPencil_requested hCond hN hL state strong
    hStrongMatrix slot hBase hKept relabeling contracted hConnected
  obtain ⟨w', hw'⟩ := DraismaVargas.SubdivisionPencil.exists_of_BNExists (spec := spec)
    w.scale_pos ((hbn w.scale w.scale_pos 1 (degree : ℤ)).mp w.bnExists)
  exact ⟨w', hw'.trans hw⟩

end Terminal

/-! ## 6.  The expansion model, packaged with the producer and the transport -/

section Model

variable {n₁ p₁ : ℕ}

/-- **The two ends meet.**  For an arbitrary connected requested specification
of genus at least two, `RequestedExpandedEndpoints.exists_expansionModel`
returns a reduced representative `spec₀` and an
expansion datum whose `bigSpec` is a cubic loopless connected model, such that

* the requested slots are distributed over the retained cubic slots
  (`RetainedIndex`), which is exactly what
  `InputRefinementData.Retained.inputRefinement` consumes, with **no** further
  hypothesis, and
* rank one in any degree at any scale on `spec₀` is a `SubdivisionPencil` of
  the original request at that same scale. -/
theorem exists_expansionModel_retainedIndex (spec : Spec n₁ p₁)
    (hConn : spec.core.Connected) (hGenus : n₁ < p₁) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀)))
      (hN : 0 < 2 * (p₀ - n₀))
      (hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e),
      D.Conditions spec₀.core ∧ D.bigCore.Cubic ∧ D.bigCore.Connected ∧
        (p₀ : ℤ) - n₀ = (p₁ : ℤ) - n₁ ∧
        Nonempty (RetainedIndex (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀) ∧
        (∀ (d k : ℕ) (hk : 0 < k), BNExists (spec₀.scale k hk).graph 1 (d : ℤ) →
          ∃ pencil : DraismaVargas.SubdivisionPencil spec d, pencil.scale = k) := by
  obtain ⟨n₀, p₀, spec₀, D, hCond, hCubic, hConnBig, hL, hN, -, -, hg₀, -, hbns₀⟩ :=
    exists_expansionModel spec hConn hGenus
  refine ⟨n₀, p₀, spec₀, D, hN, hL, hCond, hCubic, hConnBig, hg₀,
    ⟨retainedIndex hCond hN hL⟩, ?_⟩
  intro d k hk hBN
  exact DraismaVargas.SubdivisionPencil.exists_of_BNExists (spec := spec) hk
    ((hbns₀ k hk 1 (d : ℤ)).mp hBN)

end Model

end DraismaVargas.LocalCases.RetainedIndexProducer
