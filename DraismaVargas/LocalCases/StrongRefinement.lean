import DraismaVargas.LocalCases.TraversalPresentation

/-!
# Faithful and spanning core dictionaries

An input refinement at a cleared face asks for the subdivision of the scaled
requested specification to be Laplacian-equivalent to the contracted quotient
source.  `TraversalPresentation.StrongPresentation` together with
`TraversalPresentation.CoreDictionary` places the stable core on the quotient
source, and this file asks whether that is enough to determine the graph to be
presented.

## The verdict

**No, and the obstruction is one missing field: the core dictionary's
`vertexAt` is not required to be injective.**

A construction reading only `InputRefinementData.InputInterface` is impossible,
because `spec.core` is invisible there.  `CoreDictionary` repairs precisely
that: its `vertexAt`, `tail_eq` and `head_eq` place the stable core on the
quotient source and pin the two ends of the row displaying slot `i` to the two
ends of `i`.  What it pins down is therefore the **pushforward** of `spec.core`
along `vertexAt`, and nothing more.  Pushing a core forward along a
*non-injective* map changes the graph, so the obstruction survives:

* `not_exists_common_target_of_dictionary` (§4) — no single graph is
  Laplacian-equivalent to the subdivision of every `Spec 4 3` carrying a fixed
  length function **and a fixed core dictionary**.  The two witnesses are
  `specUnfolded`, whose three slots run between four distinct core vertices, and
  `specFolded`, which routes two of them through the same pair and so carries a
  doubled edge; they share a length function, a vertex placement `dictVertex`,
  and the row-end data `rowStart`, `rowFinish`, and they are not
  Laplacian-equivalent.  The quotient source they both purport to model is a
  theta graph — two junctions of surviving valency three joined by three maximal
  stable paths — so the witnesses are compatible with
  `FullDimensionalSource`'s trivalence bound as well as with
  `W4StableSource.IsPathEnd`.
* `not_exists_construction` (§4) is the same statement with the quantifier
  structure made explicit: *every* source-side datum is held fixed while `spec`
  varies, so no strengthening of the source-side hypotheses can help.  In
  particular a compatibility of the target occurrences under a row with the
  coordinate labelling of that row is powerless here, being a condition on the
  presentation alone.

The witnesses are chosen so that **the obvious numerical invariants are blind to
the difference**: the two specifications have the same slot lengths
(`length_specFolded`), the same number of edges and hence the same total length
(`card_edges_eq`), the same genus (`genus_eq`), and the same vertex count
(`card_vertices_eq`).  What separates them is a doubled edge, which is exactly
what a non-injective `vertexAt` creates.

## The missing field, stated

`Faithful dictionary : Function.Injective dictionary.vertexAt` — *distinct
stable core vertices sit at distinct quotient-source vertices*.  This is the
content of "`spec.core` is the stable model of the quotient source" that
`CoreDictionary` leaves out, and it is exactly the dividing line:

* without it, §3–§4;
* with it, `core_eq_of_injective` and `core_eq_of_coreDictionary` (§2): any two
  specifications of the same shape carrying the same placement have the *same
  core*, and with equal lengths are the same specification
  (`eq_of_injective`).  `exists_relabel_of_injective` is the version for two
  different placements with the same image, where the core is determined up to a
  relabelling of `Fin n`.

`Spanned`, and its dictionary form `Spanning` (§1) — no stable core vertex is
placed away from the row ends — is the second half of what "stable model" means,
and is what makes two dictionaries comparable (`exists_relabel_of_spanned`).  The
counterexample of §3 **satisfies** `Spanned` (`spanned_dictVertex`) and fails
only `Faithful` (`not_injective_dictVertex`), so faithfulness alone is already
indispensable.  The three conditions are jointly satisfiable (`coreCompatible_id`,
`injective_id`, `spanned_id_specUnfolded`).

`Faithful` is not an idle field: `start_ne_finish_of_faithful` (§2) shows it
forces **no displayed row to be closed**, which neither `StrongPresentation` nor
`CoreDictionary` says — `head_isPathEnd` and `getLast_isPathEnd` are both
satisfied by naming the same end of a one-occurrence row twice.  That is a
necessary condition on the source, checkable before any construction exists.

## Sufficiency is not claimed here

Nothing here asserts that a faithful, spanning core dictionary *suffices*.
Determinacy is not construction: even with `Faithful` the identification still
has to match every contraction class of the source against a vertex of the
refined specification, and `CoreDictionary` says nothing about the classes that
carry no surviving occurrence at all.  What §2 establishes is only that the
obstruction of §4 — a *genuine* obstruction — disappears exactly when `vertexAt`
becomes injective.  The construction itself is carried out downstream:
`ClassInjectivity` shows that for a spanning placement the canonical class map
is injective exactly when the placement is faithful, and `TerminalExhausts`
reduces the exhaustion of the kept classes to a genus identity.

## Relation to the rest of the library

* `FullDimensionalSource.false_of_auxR0SourceInput` is the other precedent in
  this library for a theorem whose content is that something cannot be done from
  where it stands.
* `Faithful` and `Spanning` are the two conditions `CertifiedPencil` carries,
  `ClassInjectivity` and `TerminalExhausts` consume, and
  `TerminalIdentification` produces at the requested core.
-/

namespace DraismaVargas.LocalCases.StrongRefinement

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.TraversalPresentation

/-! ## 1.  The dictionary content, distilled

`TraversalPresentation.CoreDictionary` has three fields — `vertexAt`,
`tail_eq`, `head_eq` — and they are the whole of what the dictionary says about
`spec`; they say exactly this: the pushforward of `spec.core` along `vertexAt`
is the row-end data of the strong presentation.  `CoreCompatible` is that
statement with the surrounding
apparatus removed, so that the question "does this determine `spec.core`?" can
be asked and answered. -/

section Distilled

variable {n p : ℕ} {V : Type*}

/-- **What a core dictionary says about `spec`.**  The placement `vertexAt`
carries the tail of stable slot `i` to the vertex the displaying row starts at,
and its head to the vertex the row finishes at. -/
def CoreCompatible (vertexAt : Fin n → V) (start finish : Fin p → V)
    (spec : Spec n p) : Prop :=
  (∀ i : Fin p, vertexAt (spec.core.tail i) = start i) ∧
    ∀ i : Fin p, vertexAt (spec.core.head i) = finish i

/-- **No stable core vertex sits away from the row ends.**  Together with
`CoreCompatible` this says the image of the placement *is* the set of row ends;
see `range_eq_of_spanned`. -/
def Spanned (vertexAt : Fin n → V) (start finish : Fin p → V) : Prop :=
  ∀ v : Fin n, (∃ i : Fin p, vertexAt v = start i) ∨ ∃ i : Fin p, vertexAt v = finish i

end Distilled

section Bridge

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ} {spec : Spec n p}
  {strong : StrongPresentation candidate.datum coordinate}
  {F : Finset (Fin p)}
  {iface : InputInterface spec strong.toPresentation coordinates F}
  {face : ClearedFace candidate strong.toPresentation coordinates}

/-- **The bridge.**  A `TraversalPresentation.CoreDictionary` is a
`CoreCompatible` placement for the row ends the strong presentation names, and
this is the whole of the dictionary's constraint on the stable
specification. -/
theorem coreCompatible_of_coreDictionary
    (dictionary : CoreDictionary spec strong iface) :
    CoreCompatible dictionary.vertexAt (fun i ↦ strong.start (iface.slot i))
      (fun i ↦ strong.finish (iface.slot i)) spec :=
  ⟨dictionary.tail_eq, dictionary.head_eq⟩

/-- **The missing field.**  Distinct stable core vertices sit at distinct
quotient-source vertices.  This is what `CoreDictionary` does not ask for, what
§3 shows cannot be derived, and what §2 shows is exactly enough to pin the core
down. -/
def Faithful (dictionary : CoreDictionary spec strong iface) : Prop :=
  Function.Injective dictionary.vertexAt

/-- and the second half of "stable model": no stable core vertex is placed away
from the ends of the displayed rows. -/
def Spanning (dictionary : CoreDictionary spec strong iface) : Prop :=
  Spanned dictionary.vertexAt (fun i ↦ strong.start (iface.slot i))
    (fun i ↦ strong.finish (iface.slot i))

end Bridge

/-! ## 2.  Faithfulness determines the core

The three statements of this section are the positive half of the answer, and
they are about **determinacy**, not construction: a faithful placement leaves no
freedom in `spec.core`, so the obstruction exhibited in §3 is the only one that a
core dictionary fails to remove. -/

section Determinacy

variable {n p : ℕ} {V : Type*} {vertexAt : Fin n → V} {start finish : Fin p → V}
  {first second : Spec n p}

/-- **Faithfulness pins the core down.**  Two stable specifications placed on the
quotient source by the *same* injective placement, with the same row ends, have
the same core. -/
theorem core_eq_of_injective (hInjective : Function.Injective vertexAt)
    (hFirst : CoreCompatible vertexAt start finish first)
    (hSecond : CoreCompatible vertexAt start finish second) :
    first.core = second.core := by
  have hTail : first.core.tail = second.core.tail :=
    funext fun i ↦ hInjective ((hFirst.1 i).trans (hSecond.1 i).symm)
  have hHead : first.core.head = second.core.head :=
    funext fun i ↦ hInjective ((hFirst.2 i).trans (hSecond.2 i).symm)
  calc first.core = ⟨first.core.tail, first.core.head⟩ := rfl
    _ = ⟨second.core.tail, second.core.head⟩ := by rw [hTail, hHead]
    _ = second.core := rfl

/-- and with the slot lengths — which `InputInterface.matrixMap` supplies — the
whole specification.  Every remaining field of `Spec` is a proposition. -/
theorem eq_of_injective (hLength : first.length = second.length)
    (hInjective : Function.Injective vertexAt)
    (hFirst : CoreCompatible vertexAt start finish first)
    (hSecond : CoreCompatible vertexAt start finish second) :
    first = second := by
  have hCore := core_eq_of_injective hInjective hFirst hSecond
  obtain ⟨firstCore, firstLength, firstNonempty, firstLoopless, firstPos⟩ := first
  obtain ⟨secondCore, secondLength, secondNonempty, secondLoopless, secondPos⟩ := second
  simp only at hCore hLength
  subst hCore
  subst hLength
  rfl

/-- **Two faithful placements differ by a relabelling.**  If the two dictionaries
reach the same quotient-source vertices, the cores agree after a permutation of
`Fin n`; `exists_relabel_of_spanned` supplies the hypothesis on the images from
`Spanned`. -/
theorem exists_relabel_of_injective {firstAt secondAt : Fin n → V}
    (hFirstInjective : Function.Injective firstAt)
    (hSecondInjective : Function.Injective secondAt)
    (hRange : Set.range firstAt = Set.range secondAt)
    (hFirst : CoreCompatible firstAt start finish first)
    (hSecond : CoreCompatible secondAt start finish second) :
    ∃ relabel : Fin n ≃ Fin n,
      (∀ i : Fin p, relabel (first.core.tail i) = second.core.tail i) ∧
        ∀ i : Fin p, relabel (first.core.head i) = second.core.head i := by
  classical
  set relabel : Fin n ≃ Fin n :=
    (Equiv.ofInjective firstAt hFirstInjective).trans
      ((Equiv.setCongr hRange).trans
        (Equiv.ofInjective secondAt hSecondInjective).symm) with hRelabel
  have hKey : ∀ v : Fin n, secondAt (relabel v) = firstAt v := by
    intro v
    have hApply := (Equiv.ofInjective secondAt hSecondInjective).apply_symm_apply
      (Equiv.setCongr hRange ⟨firstAt v, Set.mem_range_self v⟩)
    have hSubtype :
        (⟨secondAt (relabel v), Set.mem_range_self _⟩ : Set.range secondAt) =
          Equiv.setCongr hRange ⟨firstAt v, Set.mem_range_self v⟩ := by
      rw [hRelabel]
      exact hApply
    exact congrArg Subtype.val hSubtype
  exact ⟨relabel,
    fun i ↦ hSecondInjective ((hKey _).trans ((hFirst.1 i).trans (hSecond.1 i).symm)),
    fun i ↦ hSecondInjective ((hKey _).trans ((hFirst.2 i).trans (hSecond.2 i).symm))⟩

/-- A spanning placement reaches exactly the row ends. -/
theorem range_eq_of_spanned (hCompatible : CoreCompatible vertexAt start finish first)
    (hSpanned : Spanned vertexAt start finish) :
    Set.range vertexAt = Set.range start ∪ Set.range finish := by
  refine Set.Subset.antisymm (fun value hValue ↦ ?_) (fun value hValue ↦ ?_)
  · obtain ⟨v, hv⟩ := hValue
    rcases hSpanned v with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨i, by rw [← hi, hv]⟩
    · exact Or.inr ⟨i, by rw [← hi, hv]⟩
  · rcases hValue with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨first.core.tail i, (hCompatible.1 i).trans hi⟩
    · exact ⟨first.core.head i, (hCompatible.2 i).trans hi⟩

/-- **Faithful and spanning determine the core up to a relabelling**, for two
dictionaries that need not agree. -/
theorem exists_relabel_of_spanned {firstAt secondAt : Fin n → V}
    (hFirstInjective : Function.Injective firstAt)
    (hSecondInjective : Function.Injective secondAt)
    (hFirst : CoreCompatible firstAt start finish first)
    (hSecond : CoreCompatible secondAt start finish second)
    (hFirstSpanned : Spanned firstAt start finish)
    (hSecondSpanned : Spanned secondAt start finish) :
    ∃ relabel : Fin n ≃ Fin n,
      (∀ i : Fin p, relabel (first.core.tail i) = second.core.tail i) ∧
        ∀ i : Fin p, relabel (first.core.head i) = second.core.head i :=
  exists_relabel_of_injective hFirstInjective hSecondInjective
    ((range_eq_of_spanned hFirst hFirstSpanned).trans
      (range_eq_of_spanned hSecond hSecondSpanned).symm)
    hFirst hSecond

end Determinacy

section DeterminacyDictionary

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {wall : target.V} {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ} {n p : ℕ}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}

/-- **The same, read at the real structures.**  A faithful core dictionary
determines the stable core: two specifications carrying the same slot labelling
and the same placement have the same core.  Without `hFaithful` this is false,
by §4. -/
theorem core_eq_of_coreDictionary {first second : Spec n p}
    {ifaceFirst : InputInterface first strong.toPresentation coordinates}
    {ifaceSecond : InputInterface second strong.toPresentation coordinates}
    (dictionaryFirst : CoreDictionary first strong ifaceFirst)
    (dictionarySecond : CoreDictionary second strong ifaceSecond)
    (hSlot : ifaceFirst.slot = ifaceSecond.slot)
    (hPlacement : dictionaryFirst.vertexAt = dictionarySecond.vertexAt)
    (hFaithful : Faithful dictionaryFirst) :
    first.core = second.core := by
  refine core_eq_of_injective hFaithful
    (coreCompatible_of_coreDictionary dictionaryFirst) ?_
  have hCompatible := coreCompatible_of_coreDictionary dictionarySecond
  rw [← hPlacement, ← hSlot] at hCompatible
  exact hCompatible

/-- **What faithfulness forces on the source.**  No displayed row is closed: the
vertex a row starts at is not the vertex it finishes at.  `StrongPresentation`
does *not* say this — `head_isPathEnd` and `getLast_isPathEnd` are satisfied by
naming the same end twice — and neither does `CoreDictionary`; it is
`Spec.core_loopless` transported through an injective placement.

It is a necessary condition, checkable against the source before any
construction exists. -/
theorem start_ne_finish_of_faithful {spec : Spec n p}
    {iface : InputInterface spec strong.toPresentation coordinates}
    (dictionary : CoreDictionary spec strong iface)
    (hFaithful : Faithful dictionary) (i : Fin p) :
    strong.start (iface.slot i) ≠ strong.finish (iface.slot i) := by
  intro hEq
  refine spec.core_loopless i (hFaithful ?_)
  rw [dictionary.tail_eq i, dictionary.head_eq i, hEq]

end DeterminacyDictionary

/-! ## 3.  The freedom a core dictionary leaves

Two stable specifications on four core vertices and three unit slots, with the
*same* placement `dictVertex` onto a two-element set of quotient-source
junctions and the same row-end data.  `specUnfolded` spreads the three slots over
four distinct core vertices — a path `3 — 0 — 2 — 1`; `specFolded` routes two of
them through the same pair — a doubled edge with a pendant edge and one core
vertex left isolated.  They have the same slot lengths, the same number of
vertices, the same number of edges and the same genus.  The placement is not
injective, and that is the only difference.

The picture: a theta-shaped quotient source, two junctions joined by three
maximal stable paths.  Each junction carries three row ends, so its surviving
valency is three — within `FullDimensionalSource`'s trivalence bound
`nonDanglingValency ≤ 3`, and different from two as `W4StableSource.IsPathEnd`
and hence `StrongPresentation.head_isPathEnd` demand.  All three rows run from
the first junction to the second.  Both specifications claim to be the stable
model of that source, with the same dictionary, and nothing in the data tells
them apart. -/

section Independence

/-- The core of a path on four vertices, `3 — 0 — 2 — 1`. -/
def coreUnfolded : ExplicitPotential.Core 4 3 where
  tail := ![0, 0, 1]
  head := ![2, 3, 2]

/-- The core of a doubled edge with a pendant edge and an isolated vertex. -/
def coreFolded : ExplicitPotential.Core 4 3 where
  tail := ![0, 0, 0]
  head := ![2, 2, 3]

/-- The three slots spread over four distinct core vertices, presented as a unit
subdivision. -/
def specUnfolded : Spec 4 3 where
  core := coreUnfolded
  length := fun _ ↦ 1
  core_nonempty := by norm_num
  core_loopless := by decide
  length_pos := by decide

/-- Two of the three slots folded onto one pair of core vertices.  Its slot
lengths are those of `specUnfolded`. -/
def specFolded : Spec 4 3 where
  core := coreFolded
  length := fun _ ↦ 1
  core_nonempty := by norm_num
  core_loopless := by decide
  length_pos := by decide

/-- The placement of the four stable core vertices on the two junctions of the
quotient source.  It is **not** injective, and that is the whole point. -/
def dictVertex : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The junction each displayed row starts at. -/
def rowStart : Fin 3 → Fin 2 := ![0, 0, 0]

/-- The junction each displayed row finishes at. -/
def rowFinish : Fin 3 → Fin 2 := ![1, 1, 1]

theorem length_specFolded : specUnfolded.length = specFolded.length := rfl

/-- The unfolded specification is compatible with the placement. -/
theorem coreCompatible_specUnfolded :
    CoreCompatible dictVertex rowStart rowFinish specUnfolded := by
  constructor <;> decide

/-- and so is the folded one, with the *same* placement and the same row
ends. -/
theorem coreCompatible_specFolded :
    CoreCompatible dictVertex rowStart rowFinish specFolded := by
  constructor <;> decide

/-- Every stable core vertex is placed at a row end: `Spanned` holds, so it is
not the condition that fails. -/
theorem spanned_dictVertex : Spanned dictVertex rowStart rowFinish := by
  unfold Spanned
  decide

/-- The placement is not injective: the first two stable core vertices are placed
at the same junction.  By §2 this is the only thing that can go wrong — restore
injectivity and the two specifications are forced to coincide. -/
theorem not_injective_dictVertex : ¬ Function.Injective dictVertex := by
  intro hInjective
  have hEq : (0 : Fin 4) = 1 := hInjective (a₁ := 0) (a₂ := 1) rfl
  exact absurd hEq (by decide)

/-! ### Joint satisfiability

`CoreCompatible`, `Faithful` and `Spanned` hold simultaneously, realized by the
placement that does nothing: a specification sits on its own core, injectively,
and every core vertex of `specUnfolded` is an endpoint of a slot.  So the
conditions of §2 do not contradict each other, and the counterexample above is a
statement about what is *missing*, not about what is impossible. -/

/-- Every specification is compatible with the identity placement and its own
endpoint data. -/
theorem coreCompatible_id {n p : ℕ} (spec : Spec n p) :
    CoreCompatible (id : Fin n → Fin n) spec.core.tail spec.core.head spec :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- which is faithful. -/
theorem injective_id {n : ℕ} : Function.Injective (id : Fin n → Fin n) :=
  fun _ _ hEq ↦ hEq

/-- and, on the unfolded specification, spanning. -/
theorem spanned_id_specUnfolded :
    Spanned (id : Fin 4 → Fin 4) specUnfolded.core.tail specUnfolded.core.head := by
  unfold Spanned
  decide

/-! ### The counterexample passes the numerical checks

A relabelling of specifications preserves the total length, the genus and the
slot count.  All three read only data on which the two specifications agree. -/

/-- Same number of edges, so the total length cannot separate them. -/
theorem card_edges_eq :
    specUnfolded.graph.edges.card = specFolded.graph.edges.card := by
  rw [Spec.card_edges, Spec.card_edges, length_specFolded]

/-- Same number of vertices. -/
theorem card_vertices_eq :
    Fintype.card specUnfolded.graph.V = Fintype.card specFolded.graph.V := by
  rw [Spec.card_vertices, Spec.card_vertices, length_specFolded]

/-- Same genus, so the genus cannot separate them either. -/
theorem genus_eq : genus specUnfolded.graph = genus specFolded.graph := by
  rw [Spec.genus_graph, Spec.genus_graph]

/-- The doubled edge. -/
theorem num_edges_specFolded :
    num_edges specFolded.graph (specFolded.coreVertex 0)
      (specFolded.coreVertex 2) = 2 := by
  decide

/-- The unfolded specification has none. -/
theorem num_edges_specUnfolded_le_one (first second : specUnfolded.graph.V) :
    num_edges specUnfolded.graph first second ≤ 1 := by
  revert first second
  decide

/-- **The two specifications are not Laplacian-equivalent**, so they are not
interchangeable as the target of the input refinement. -/
theorem not_laplacianEquiv_specUnfolded_specFolded :
    IsEmpty (LaplacianEquiv specUnfolded.graph specFolded.graph) := by
  refine ⟨fun equivalence ↦ ?_⟩
  have hEdges := equivalence.num_edges_eq
    (equivalence.toEquiv.symm (specFolded.coreVertex 0))
    (equivalence.toEquiv.symm (specFolded.coreVertex 2))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, num_edges_specFolded]
    at hEdges
  have hBound := num_edges_specUnfolded_le_one
    (equivalence.toEquiv.symm (specFolded.coreVertex 0))
    (equivalence.toEquiv.symm (specFolded.coreVertex 2))
  omega

end Independence

/-! ## 4.  The graph to be presented is not a function of the dictionary either

No common target exists even when the two witnesses must share a core
dictionary as well as a slot-length function. -/

section Obstruction

/-- **A core dictionary does not determine the graph to be presented.**  No
graph is Laplacian-equivalent to the subdivision of every specification carrying
a given slot-length function *and a given core dictionary*: the unfolded and the
folded specification carry the same ones.

`Spec.scale` does not touch the core (`Spec.scale_core`), so scaling the input by
the face's common denominator does not change this. -/
theorem not_exists_common_target_of_dictionary :
    ¬ ∃ presented : CFGraph, ∀ spec : Spec 4 3,
        spec.length = specUnfolded.length →
          CoreCompatible dictVertex rowStart rowFinish spec →
            Nonempty (LaplacianEquiv spec.graph presented) := by
  rintro ⟨presented, hAll⟩
  obtain ⟨first⟩ := hAll specUnfolded rfl coreCompatible_specUnfolded
  obtain ⟨second⟩ := hAll specFolded length_specFolded coreCompatible_specFolded
  exact not_laplacianEquiv_specUnfolded_specFolded.elim (first.trans second.symm)

/-- **No construction, however much source-side data it reads.**  `Source` stands
for any aggregate of source-side inputs — the gluing datum, the strong
presentation, the cleared face, the contraction topology, trivalence, a
compatibility of target occurrences with the coordinate labelling, anything at
all — and `presented` for the graph such a construction would present.
All of it is held fixed while `spec` varies over the specifications the dictionary
admits, so no strengthening of the source-side hypotheses can remove the
obstruction.  Only a condition tying `spec` more tightly to the source can, and
`Faithful` (§2) is such a condition. -/
theorem not_exists_construction {Source : Type*} (presented : Source → CFGraph)
    (source : Source) :
    ¬ ∀ spec : Spec 4 3, spec.length = specUnfolded.length →
        CoreCompatible dictVertex rowStart rowFinish spec →
          Nonempty (LaplacianEquiv spec.graph (presented source)) :=
  fun hAll ↦ not_exists_common_target_of_dictionary ⟨presented source, hAll⟩

end Obstruction

/-! ## 5.  Summary

Of the data a stable core dictionary consists of:

* the decomposition of the rows, their chaining, and the incidence of their
  first and last occurrences are supplied by
  `TraversalPresentation.StrongPresentation`, and by `ofLabelling` they are
  realized by the honest traversal;
* the placement `vertexAt` with `tail_eq`, `head_eq` is
  `TraversalPresentation.CoreDictionary`, and it is **not enough**: §4.

The one field that has to be added is `Faithful`.  With it the stable core is
determined (§2); without it it is not (§4).  This is the sharpest hypothesis
this file can state, and it is a hypothesis, not a theorem: like
`W4StableSource.HasPathEnds` and
`FullDimensionalSource.FullDimensionalSourcePresentation.trivalent`, it says
something about the quotient source that no field of the presentation implies.

Whether a faithful, spanning core dictionary suffices is **not** claimed here.
Determinacy is not construction: the identification still has to exhaust the
contraction classes of the source, and in particular says nothing about classes
carrying no surviving occurrence at all.  `Faithful` is used exactly at the
point where a stable core vertex is sent to a contraction class
(`ClassInjectivity`). -/

end DraismaVargas.LocalCases.StrongRefinement
