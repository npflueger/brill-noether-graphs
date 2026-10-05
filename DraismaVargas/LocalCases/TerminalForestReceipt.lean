module

public import DraismaVargas.LocalCases.ZeroForestPreservation
public import DraismaVargas.LocalCases.ZeroFreeTerminalFace

@[expose] public section

/-!
# Where the terminal face's forest receipt can and cannot come from

At a terminal state of the march, the cleared face
`ZeroFreeTerminalFace.clearedFaceOfTerminal` needs the forest receipt

```
IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
  (clearedFaceOfTerminal hTerminal candidate presentation).realization.sourceZeroSet
```

This file settles what that receipt actually depends on.  There are three
conceivable sources for it: an argument at the endpoint comparing with a face
already known to be acyclic (route 1), an invariant carried along the march
(route 2), and a statement about the local source over the vanishing columns
(route 3).  The sections below take them in the order in which they turn out
to matter.

## 1.  The receipt depends on the endpoint only through its vanishing columns

`Candidate.ClearedFace.mem_sourceZeroSet_iff` says a canonical quotient-source
slot is a zero slot exactly when the coordinate over it vanishes.  So the zero
set of a cleared face is `slotsOver data presentation (zeroColumns coordinates)`
(`sourceZeroSet_eq_slotsOver`) — a function of the *finite set of vanishing
columns* and of nothing else about the endpoint.  Two consequences:

* `sourceZeroSet_eq_of_zero_iff` — endpoints with the same vanishing pattern
  have literally the same zero set;
* `isForest_of_zero_imp` — the receipt transfers *down* along inclusion of
  vanishing patterns (`ZeroForestBridge.isForest_of_subset`).

`isForest_of_currentFinish_zero_imp` is the resulting sharpening of the
zero-free case `isForest_of_currentFinish_ne_zero`: it is the weakest form
route 1 can take, and it makes plain that a route-1 argument must exhibit a
*superset* of the vanishing columns whose fibre is already known acyclic.
The zero-free case is the instance in which that superset is empty.

## 2.  The receipt is a genuine condition: it can fail

`not_isForest_of_redundant` — a slot whose endpoints are already joined by the
other slots of `F` makes `F` a non-forest — and its corollary
`not_isForest_of_parallel` give the exact local obstruction.  Transported to a
cleared face (`not_isForest_sourceZeroSet_of_parallel`) it reads: *if two
distinct source occurrences lying over vanishing target columns have the same
pair of quotient-source endpoints, the receipt is false*, so no terminal face
with such a pair carries it.

A "banana over a vanishing column" is therefore fatal, and no amount of march
bookkeeping can produce the receipt at such a face.  This is what rules route 2
out in its naive form: an invariant carried along the march would have to be
*established* somewhere, and the only thing that can establish it is a
statement about the source over the vanishing columns.  Read the other way
(`injOn_sourceEnds_of_isForest`) this is the necessary condition the receipt
imposes on whoever supplies it: distinct vanishing source occurrences must join
distinct pairs of quotient-source vertices.

## 3.  What the march does supply for free

A march state carries `currentFinish_map : (matrix label).mulVec currentFinish
= baseFinish`, and `baseFinish` is the same vector at every state — it is the
requested stable metric, whose positivity is `Spec.length_pos`.  Combined with
`Candidate.ClearedFace.sourcePathLength_eq_scale_mul` this gives, with no new
field whatsoever,

```
exists_sourceLength_ne_zero_of_baseFinish_ne_zero :
  baseFinish row ≠ 0 → ∃ edge ∈ presentation.path row, sourceLength edge ≠ 0
```

— *no displayed row of the presentation is entirely swallowed by the zero set*
(`exists_notMem_sourceZeroSet_of_baseFinish_ne_zero` in slot form).  That is
the arithmetic half of the honest DV argument.  The other half — that every
cycle of the quotient source is a union of complete displayed rows — is an
**incidence/ordering condition on `GluingDatum.LengthMatrixPresentation`**,
the condition `PresentationDecomposition` isolates.  For a strong presentation
`CycleRows` proves it, and `SourceFibreForest.isForest_of_nonzero_rows`
combines the two halves.

## The verdict

Route 3, in a sharper form than "a local-source obligation": the receipt is not
a march field and cannot be one (§2), the march already supplies its arithmetic
half (§3), and what remains is the incidence structure on the presentation
described there.  §4 below nevertheless states, in Lean, the exact field a
march state would have to carry if one insisted on route 2 —
`ZeroFibreForest` — together with the proof (`zeroFibreForest_iff_isForest`)
that at a terminal state it is precisely the forest receipt.
-/

namespace DraismaVargas.LocalCases.TerminalForestReceipt

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.SemanticAtlasMarch

/-! ## 0.  Census forest = acyclic, both directions

`Utilities.Certificate.ContractionForestCensusGeneral` proves the
graphic-matroid rank *inequality* `n ≤ #classes + F.card`
(`card_le_card_image_compFold_add_card`), defines `IsForest F` to be its
equality case, and derives the consequences of `IsForest`.  It never relates
`IsForest` to acyclicity in either direction.  This section supplies both.

*Cycle ⟹ not a forest* (`not_isForest_of_redundant`, and the parallel-slot
special case `not_isForest_of_parallel`): deleting a redundant slot leaves the
vertex partition unchanged while dropping the cardinality by one, which the
rank inequality forbids for a forest.

*Acyclic ⟹ forest* (`isForest_of_acyclic`, packaged with the converse as
`isForest_iff_acyclic`, and consumed as `exists_redundant_of_not_isForest`:
**a slot set that is not a census forest carries a redundant slot**).  The
proof is the union-find induction: erasing a non-redundant slot strictly
increases the number of classes (`card_image_compFold_lt_of_not_reachIn`), so
the rank inequality is saturated all the way down to `∅`.  No `decide`, no
shape-specific work; everything here is stated for an arbitrary
`ExplicitPotential.Core n p`.

The section then isolates the facts about a *minimal* non-forest `C` that the
row argument in `CycleRows` consumes:

* `exists_minimal_not_isForest` — every non-forest contains a minimal one;
* `exists_ne_slotAt_of_minimal` — every core vertex met by a slot of `C` is met
  by a second one (a pendant slot could be erased);
* `notMem_of_separated` — a bridge never belongs to `C`;
* `ZeroFreeTerminalFace.isForest_empty` — so a minimal non-forest is nonempty.

Both of the last two come from `isForest_of_not_reachIn_erase`.

These are general facts about `ContractionForestCensusGeneral`: the converse
half is the other half of the graphic-matroid rank equation whose inequality is
`card_le_card_image_compFold_add_card`, and `reachIn_mono` below also appears
there, as an implicit-`core` variant. -/

section Census

variable {n p : ℕ} (core : ExplicitPotential.Core n p)

/-- Reachability through `F` is reachability through `F.erase drop`, as soon as
the endpoints of `drop` are already joined by the surviving slots. -/
theorem reachIn_erase_of_redundant {F : Finset (Fin p)} {drop : Fin p}
    (hReach : ReachIn core (F.erase drop) (core.tail drop) (core.head drop))
    {x y : Fin n} (h : ReachIn core F x y) :
    ReachIn core (F.erase drop) x y := by
  have hStep : ∀ u v : Fin n, AdjInList core (edgeList F) u v →
      ReachIn core (F.erase drop) u v := by
    intro u v hAdj
    obtain ⟨slot, hSlot, hEnds⟩ := hAdj
    rw [mem_edgeList] at hSlot
    by_cases hDrop : slot = drop
    · subst hDrop
      rcases hEnds with ⟨hTail, hHead⟩ | ⟨hHead, hTail⟩
      · exact hTail ▸ hHead ▸ hReach
      · exact hHead ▸ hTail ▸ reachInList_symmetric _ _ hReach
    · refine Relation.ReflTransGen.single ⟨slot, ?_, hEnds⟩
      exact (mem_edgeList _ slot).mpr (Finset.mem_erase.mpr ⟨hDrop, hSlot⟩)
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hLast ih => exact ih.trans (hStep _ _ hLast)

/-- The vertex partition is unchanged by deleting a redundant slot. -/
theorem card_image_compFold_erase_of_redundant {F : Finset (Fin p)} {drop : Fin p}
    (hReach : ReachIn core (F.erase drop) (core.tail drop) (core.head drop)) :
    (Finset.image (compFold core (F.erase drop)) Finset.univ).card
      = (Finset.image (compFold core F) Finset.univ).card := by
  have hMono : ∀ x y : Fin n, ReachIn core (F.erase drop) x y → ReachIn core F x y := by
    intro x y hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hLast ih =>
      obtain ⟨slot, hSlot, hEnds⟩ := hLast
      rw [mem_edgeList] at hSlot
      exact ih.tail ⟨slot, (mem_edgeList _ slot).mpr (Finset.mem_of_mem_erase hSlot), hEnds⟩
  have hIff : ∀ x y : Fin n,
      compFold core (F.erase drop) x = compFold core (F.erase drop) y ↔
        compFold core F x = compFold core F y := by
    intro x y
    rw [compFold_iff, compFold_iff]
    exact ⟨hMono x y, reachIn_erase_of_redundant core hReach⟩
  exact le_antisymm
    (card_image_le_of_rep_iff (compFold_idem core _) hIff)
    (card_image_le_of_rep_iff (compFold_idem core _) fun x y ↦ (hIff x y).symm)

/-- **A slot set carrying a cycle is not a census forest.**  `drop ∈ F` whose
endpoints the remaining slots already join is exactly a cycle of `F`. -/
theorem not_isForest_of_redundant {F : Finset (Fin p)} {drop : Fin p}
    (hDrop : drop ∈ F)
    (hReach : ReachIn core (F.erase drop) (core.tail drop) (core.head drop)) :
    ¬ IsForest core F := by
  intro hForest
  have hPos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) (core.tail drop).isLt
  have hAdd := forest_image_add_card_eq core hForest
  have hRank := card_le_card_image_compFold_add_card core (F.erase drop)
  have hCard : (F.erase drop).card + 1 = F.card := by
    rw [Finset.card_erase_of_mem hDrop]
    exact Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨drop, hDrop⟩)
  rw [card_image_compFold_erase_of_redundant core hReach] at hRank
  omega

/-- **Two parallel slots defeat the census forest.**  The special case in which
the redundant slot is redundant because another slot of `F` joins the same pair
of vertices. -/
theorem not_isForest_of_parallel {F : Finset (Fin p)} {keep drop : Fin p}
    (hNe : keep ≠ drop) (hKeep : keep ∈ F) (hDrop : drop ∈ F)
    (hEnds : (core.tail drop = core.tail keep ∧ core.head drop = core.head keep) ∨
      (core.tail drop = core.head keep ∧ core.head drop = core.tail keep)) :
    ¬ IsForest core F := by
  refine not_isForest_of_redundant core hDrop (Relation.ReflTransGen.single ?_)
  refine ⟨keep, (mem_edgeList _ keep).mpr (Finset.mem_erase.mpr ⟨hNe, hKeep⟩), ?_⟩
  rcases hEnds with ⟨hTail, hHead⟩ | ⟨hTail, hHead⟩
  · exact Or.inl ⟨hTail.symm, hHead.symm⟩
  · exact Or.inr ⟨hTail.symm, hHead.symm⟩

/-- Census reachability is monotone in the slot set. -/
theorem reachIn_mono {F F' : Finset (Fin p)} (hSubset : F ⊆ F')
    {x y : Fin n} (hReach : ReachIn core F x y) : ReachIn core F' x y := by
  induction hReach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hLast ih =>
    obtain ⟨slot, hSlot, hEnds⟩ := hLast
    exact ih.tail ⟨slot,
      (mem_edgeList _ slot).mpr (hSubset ((mem_edgeList _ slot).mp hSlot)), hEnds⟩

/-- A vertex untouched by `F` is alone in its class: no walk leaves it. -/
theorem eq_of_reachIn_of_no_incidence {F : Finset (Fin p)} {v : Fin n}
    (hNone : ∀ slot ∈ F, core.tail slot ≠ v ∧ core.head slot ≠ v)
    {y : Fin n} (hReach : ReachIn core F v y) : y = v := by
  induction hReach with
  | refl => rfl
  | tail _ hLast ih =>
    obtain ⟨slot, hSlot, hEnds⟩ := hLast
    have hMem := (mem_edgeList _ slot).mp hSlot
    rcases hEnds with ⟨hTail, -⟩ | ⟨hHead, -⟩
    · exact absurd (hTail.trans ih) (hNone slot hMem).1
    · exact absurd (hHead.trans ih) (hNone slot hMem).2

/-- **Erasing a non-redundant slot strictly increases the class count.**  The
classes of `F.erase drop` refine those of `F`, surjectively, and the two ends of
`drop` are two distinct classes of `F.erase drop` with the same image. -/
theorem card_image_compFold_lt_of_not_reachIn {F : Finset (Fin p)} {drop : Fin p}
    (hDrop : drop ∈ F)
    (hNot : ¬ ReachIn core (F.erase drop) (core.tail drop) (core.head drop)) :
    (Finset.image (compFold core F) Finset.univ).card
      < (Finset.image (compFold core (F.erase drop)) Finset.univ).card := by
  classical
  have hKey : ∀ x : Fin n,
      compFold core F (compFold core (F.erase drop) x) = compFold core F x := by
    intro x
    refine ((compFold_iff core F x (compFold core (F.erase drop) x)).mpr ?_).symm
    exact reachIn_mono core (Finset.erase_subset _ _)
      (reachIn_self_compFold core (F.erase drop) x)
  have hNe : compFold core (F.erase drop) (core.tail drop)
      ≠ compFold core (F.erase drop) (core.head drop) := by
    intro hEq
    exact hNot ((compFold_iff core (F.erase drop) _ _).mp hEq)
  have hSame : compFold core F (compFold core (F.erase drop) (core.tail drop))
      = compFold core F (compFold core (F.erase drop) (core.head drop)) := by
    rw [hKey, hKey]
    exact compFold_tail_eq_head_of_mem core hDrop
  have hTailMem : compFold core (F.erase drop) (core.tail drop)
      ∈ Finset.image (compFold core (F.erase drop)) Finset.univ :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hHeadMem : compFold core (F.erase drop) (core.head drop)
      ∈ Finset.image (compFold core (F.erase drop)) Finset.univ :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hImage : Finset.image (compFold core F) Finset.univ
      = Finset.image (compFold core F)
        ((Finset.image (compFold core (F.erase drop)) Finset.univ).erase
          (compFold core (F.erase drop) (core.head drop))) := by
    refine Finset.Subset.antisymm (fun z hz ↦ ?_) (fun z hz ↦ ?_)
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
      by_cases hx : compFold core (F.erase drop) x
          = compFold core (F.erase drop) (core.head drop)
      · refine Finset.mem_image.mpr
          ⟨compFold core (F.erase drop) (core.tail drop),
            Finset.mem_erase.mpr ⟨hNe, hTailMem⟩, ?_⟩
        rw [hSame, ← hx, hKey]
      · exact Finset.mem_image.mpr ⟨compFold core (F.erase drop) x,
          Finset.mem_erase.mpr ⟨hx, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩,
          hKey x⟩
    · obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  rw [hImage]
  exact lt_of_le_of_lt Finset.card_image_le (Finset.card_erase_lt_of_mem hHeadMem)

/-- A slot set is **acyclic** when no slot of it is redundant, i.e. no slot has
its two ends already joined by the others.  `not_isForest_of_redundant` is the
statement that a census forest is acyclic; `isForest_of_acyclic` is the
converse. -/
def Acyclic (F : Finset (Fin p)) : Prop :=
  ∀ drop ∈ F, ¬ ReachIn core (F.erase drop) (core.tail drop) (core.head drop)

theorem Acyclic.erase {F : Finset (Fin p)} (hF : Acyclic core F) (slot : Fin p) :
    Acyclic core (F.erase slot) := by
  intro drop hDrop hReach
  refine hF drop (Finset.mem_of_mem_erase hDrop) (reachIn_mono core ?_ hReach)
  intro s hs
  obtain ⟨hNe, hMem⟩ := Finset.mem_erase.mp hs
  exact Finset.mem_erase.mpr ⟨hNe, Finset.mem_of_mem_erase hMem⟩

/-- The rank inequality is saturated on an acyclic slot set. -/
theorem card_image_compFold_add_card_le_of_acyclic :
    ∀ F : Finset (Fin p), Acyclic core F →
      (Finset.image (compFold core F) Finset.univ).card + F.card ≤ n := by
  intro F
  induction F using Finset.strongInduction with
  | _ F ih =>
    intro hF
    rcases F.eq_empty_or_nonempty with rfl | ⟨drop, hDrop⟩
    · simp [compFold_empty]
    · have hIH := ih (F.erase drop) (Finset.erase_ssubset hDrop) (Acyclic.erase core hF drop)
      have hLt := card_image_compFold_lt_of_not_reachIn core hDrop (hF drop hDrop)
      have hCard : (F.erase drop).card + 1 = F.card := by
        rw [Finset.card_erase_of_mem hDrop]
        exact Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨drop, hDrop⟩)
      omega

/-- **The census converse.**  An acyclic slot set is a census forest. -/
theorem isForest_of_acyclic {F : Finset (Fin p)} (hF : Acyclic core F) :
    IsForest core F := by
  have hSat := card_image_compFold_add_card_le_of_acyclic core F hF
  have hRank := card_le_card_image_compFold_add_card core F
  unfold IsForest
  omega

/-- **A slot set that is not a census forest carries a redundant slot.**  The
form the cycle argument consumes. -/
theorem exists_redundant_of_not_isForest {F : Finset (Fin p)}
    (hF : ¬ IsForest core F) :
    ∃ drop ∈ F, ReachIn core (F.erase drop) (core.tail drop) (core.head drop) := by
  by_contra hCon
  push Not at hCon
  exact hF (isForest_of_acyclic core fun drop hDrop ↦ hCon drop hDrop)

/-- Census forest and acyclicity are the same condition: `mp` is
`not_isForest_of_redundant` above, `mpr` is `isForest_of_acyclic`. -/
theorem isForest_iff_acyclic (F : Finset (Fin p)) :
    IsForest core F ↔ Acyclic core F :=
  ⟨fun hForest _drop hDrop hReach ↦
      not_isForest_of_redundant core hDrop hReach hForest,
    isForest_of_acyclic core⟩

/-- Erasing a non-redundant slot from a forest leaves a forest: the equality
case of the rank inequality is restored by the strict class drop. -/
theorem isForest_of_not_reachIn_erase {F : Finset (Fin p)} {drop : Fin p}
    (hDrop : drop ∈ F) (hForest : IsForest core (F.erase drop))
    (hNot : ¬ ReachIn core (F.erase drop) (core.tail drop) (core.head drop)) :
    IsForest core F := by
  have hAdd := forest_image_add_card_eq core hForest
  have hLt := card_image_compFold_lt_of_not_reachIn core hDrop hNot
  have hRank := card_le_card_image_compFold_add_card core F
  have hLe := card_image_compFold_le core F
  have hCard : (F.erase drop).card + 1 = F.card := by
    rw [Finset.card_erase_of_mem hDrop]
    exact Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨drop, hDrop⟩)
  unfold IsForest
  omega

/-- Every non-forest contains a **minimal** one: a non-forest all of whose
proper erasures are forests. -/
theorem exists_minimal_not_isForest :
    ∀ F : Finset (Fin p), ¬ IsForest core F →
      ∃ C ⊆ F, ¬ IsForest core C ∧ ∀ drop ∈ C, IsForest core (C.erase drop) := by
  intro F
  induction F using Finset.strongInduction with
  | _ F ih =>
    intro hF
    by_cases hMin : ∀ drop ∈ F, IsForest core (F.erase drop)
    · exact ⟨F, Finset.Subset.refl F, hF, hMin⟩
    · push Not at hMin
      obtain ⟨drop, hDrop, hNot⟩ := hMin
      obtain ⟨C, hSubset, hCNot, hCMin⟩ :=
        ih (F.erase drop) (Finset.erase_ssubset hDrop) hNot
      exact ⟨C, hSubset.trans (Finset.erase_subset _ _), hCNot, hCMin⟩

/-- Incidence of a census slot at a census vertex label. -/
def SlotAt (slot : Fin p) (v : Fin n) : Prop :=
  core.tail slot = v ∨ core.head slot = v

/-- **A minimal non-forest has no pendant slot.**  Every vertex met by a slot of
a minimal non-forest is met by a second one: otherwise that slot could be erased
without joining anything, and the erasure's forest equality would propagate back
up. -/
theorem exists_ne_slotAt_of_minimal {C : Finset (Fin p)}
    (hNot : ¬ IsForest core C) (hMin : ∀ drop ∈ C, IsForest core (C.erase drop))
    (hLoopless : ∀ slot : Fin p, core.tail slot ≠ core.head slot)
    {e : Fin p} (he : e ∈ C) {v : Fin n} (hv : SlotAt core e v) :
    ∃ f ∈ C, f ≠ e ∧ SlotAt core f v := by
  by_contra hCon
  push Not at hCon
  have hNone : ∀ slot ∈ C.erase e, core.tail slot ≠ v ∧ core.head slot ≠ v := by
    intro slot hSlot
    obtain ⟨hNe, hMem⟩ := Finset.mem_erase.mp hSlot
    have hSlotAt := hCon slot hMem hNe
    unfold SlotAt at hSlotAt
    push Not at hSlotAt
    exact hSlotAt
  have hNotReach :
      ¬ ReachIn core (C.erase e) (core.tail e) (core.head e) := by
    intro hReach
    rcases hv with hv | hv
    · rw [hv] at hReach
      exact hLoopless e (hv.trans (eq_of_reachIn_of_no_incidence core hNone hReach).symm)
    · have hSymm := reachInList_symmetric core (edgeList (C.erase e)) hReach
      rw [hv] at hSymm
      exact hLoopless e
        ((eq_of_reachIn_of_no_incidence core hNone hSymm).trans hv.symm)
  exact hNot (isForest_of_not_reachIn_erase core he (hMin e he) hNotReach)

/-- **A bridge is never in a minimal non-forest.**  A slot whose two ends are
separated by every slot set not containing it can be erased the same way. -/
theorem notMem_of_separated {C : Finset (Fin p)} (hNot : ¬ IsForest core C)
    (hMin : ∀ drop ∈ C, IsForest core (C.erase drop)) {e : Fin p}
    (hBridge : ∀ F : Finset (Fin p),
      ¬ ReachIn core (F.erase e) (core.tail e) (core.head e)) :
    e ∉ C :=
  fun he ↦ hNot (isForest_of_not_reachIn_erase core he (hMin e he) (hBridge C))

end Census


/-! ## 1.  The zero set is a function of the vanishing columns

`Candidate.ClearedFace.mem_sourceZeroSet_iff` is the whole content: a canonical
quotient-source slot is a zero slot exactly when the coordinate indexing the
target occurrence it lies over vanishes.  Everything in this section is
bookkeeping around that one equivalence, phrased so that it can be stated
without a face — hence without nonnegativity of the coordinate vector. -/

section Slots

variable {target : CFGraph} {degree : ℕ}

/-- The source occurrence carried by a canonical quotient-source slot.  This is
`GluingDatum.NonnegativeIntegralRealization.sourceEdgeAt` with its realization
argument dropped: that definition ignores it. -/
noncomputable def slotEdge (data : GluingDatum target degree)
    (slot : Fin data.sourceGraph.edges.card) : data.SourceEdge :=
  data.sourceEdgeOfOccurrence
    (UnitSubdivisionPresentation.edgeOccurrence data.sourceGraph slot)

theorem sourceEdgeAt_eq_slotEdge {data : GluingDatum target degree}
    (realization : data.NonnegativeIntegralRealization)
    (slot : Fin data.sourceGraph.edges.card) :
    realization.sourceEdgeAt slot = slotEdge data slot := rfl

end Slots

section Columns

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*}

/-- The column of a slot: the coordinate indexing the target occurrence the
slot lies over. -/
noncomputable def slotColumn (data : GluingDatum target degree)
    (presentation : data.LengthMatrixPresentation coordinate)
    (slot : Fin data.sourceGraph.edges.card) : coordinate :=
  presentation.targetEdge.symm (slotEdge data slot).1.1

/-- The canonical quotient-source slots lying over a set of columns. -/
noncomputable def slotsOver [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (presentation : data.LengthMatrixPresentation coordinate)
    (columns : Finset coordinate) : Finset (Fin data.sourceGraph.edges.card) :=
  Finset.univ.filter fun slot ↦ slotColumn data presentation slot ∈ columns

@[simp] theorem mem_slotsOver [DecidableEq coordinate]
    {data : GluingDatum target degree}
    {presentation : data.LengthMatrixPresentation coordinate}
    {columns : Finset coordinate} {slot : Fin data.sourceGraph.edges.card} :
    slot ∈ slotsOver data presentation columns ↔
      slotColumn data presentation slot ∈ columns := by
  simp [slotsOver]

/-- The slot fibre is monotone in the set of columns. -/
theorem slotsOver_subset [DecidableEq coordinate]
    {data : GluingDatum target degree}
    (presentation : data.LengthMatrixPresentation coordinate)
    {columns columns' : Finset coordinate} (hSubset : columns ⊆ columns') :
    slotsOver data presentation columns ⊆ slotsOver data presentation columns' := by
  intro slot hSlot
  rw [mem_slotsOver] at hSlot ⊢
  exact hSubset hSlot

/-- The vanishing columns of a coordinate vector. -/
def zeroColumns [Fintype coordinate] (x : coordinate → ℚ) : Finset coordinate :=
  Finset.univ.filter fun column ↦ x column = 0

@[simp] theorem mem_zeroColumns [Fintype coordinate] {x : coordinate → ℚ}
    {column : coordinate} :
    column ∈ zeroColumns x ↔ x column = 0 := by
  simp [zeroColumns]

theorem zeroColumns_subset [Fintype coordinate] {x y : coordinate → ℚ}
    (h : ∀ column, x column = 0 → y column = 0) :
    zeroColumns x ⊆ zeroColumns y := by
  intro column hColumn
  rw [mem_zeroColumns] at hColumn ⊢
  exact h column hColumn

end Columns

/-! ## 2.  The receipt at a cleared face

`sourceZeroSet_eq_slotsOver` is the promised identification, and the two
transfer lemmas are its consequences.  `isForest_of_zero_imp` moves an
already-known receipt **down** along inclusion of vanishing patterns, using
`ZeroForestBridge.isForest_of_subset`. -/

section Face

variable {target : CFGraph.{0}} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {x y : coordinate → ℚ}

/-- **The zero set is the slot fibre of the vanishing columns.**  In
particular it does not depend on the values of the endpoint, only on which of
its coordinates vanish. -/
theorem sourceZeroSet_eq_slotsOver
    (face : Candidate.ClearedFace candidate presentation x) :
    face.realization.sourceZeroSet =
      slotsOver candidate.datum presentation (zeroColumns x) := by
  ext slot
  rw [Candidate.ClearedFace.mem_sourceZeroSet_iff, mem_slotsOver, mem_zeroColumns]
  exact Iff.rfl

/-- Endpoints whose vanishing patterns are nested have nested zero sets. -/
theorem sourceZeroSet_subset_of_zero_imp
    (face : Candidate.ClearedFace candidate presentation x)
    (face' : Candidate.ClearedFace candidate presentation y)
    (h : ∀ column, x column = 0 → y column = 0) :
    face.realization.sourceZeroSet ⊆ face'.realization.sourceZeroSet := by
  rw [sourceZeroSet_eq_slotsOver, sourceZeroSet_eq_slotsOver]
  exact slotsOver_subset presentation (zeroColumns_subset h)

/-- Endpoints with the same vanishing pattern have literally the same zero
set. -/
theorem sourceZeroSet_eq_of_zero_iff
    (face : Candidate.ClearedFace candidate presentation x)
    (face' : Candidate.ClearedFace candidate presentation y)
    (h : ∀ column, x column = 0 ↔ y column = 0) :
    face.realization.sourceZeroSet = face'.realization.sourceZeroSet :=
  Finset.Subset.antisymm
    (sourceZeroSet_subset_of_zero_imp face face' fun column ↦ (h column).mp)
    (sourceZeroSet_subset_of_zero_imp face' face fun column ↦ (h column).mpr)

/-- **The transfer lemma.**  A census forest at a face with *more* vanishing
coordinates is a census forest at a face with fewer. -/
theorem isForest_of_zero_imp
    (face : Candidate.ClearedFace candidate presentation x)
    (face' : Candidate.ClearedFace candidate presentation y)
    (h : ∀ column, x column = 0 → y column = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face'.realization.sourceZeroSet) :
    IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet :=
  ZeroForestBridge.isForest_of_subset _
    (sourceZeroSet_subset_of_zero_imp face face' h) hForest

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- **The exact local obstruction.**  Two distinct source occurrences lying
over vanishing columns and joining the same pair of quotient-source vertices
make the receipt false. -/
theorem not_isForest_sourceZeroSet_of_parallel
    (face : Candidate.ClearedFace candidate presentation x)
    {keep drop : Fin candidate.datum.sourceGraph.edges.card} (hNe : keep ≠ drop)
    (hKeep : keep ∈ face.realization.sourceZeroSet)
    (hDrop : drop ∈ face.realization.sourceZeroSet)
    (hEnds : candidate.datum.sourceEnds (face.realization.sourceEdgeAt drop) =
      candidate.datum.sourceEnds (face.realization.sourceEdgeAt keep)) :
    ¬ IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet := by
  refine not_isForest_of_parallel _ hNe hKeep hDrop (Or.inl ⟨?_, ?_⟩)
  · refine ZeroForestPreservation.sourceVertexOf_injective candidate.datum ?_
    rw [ZeroForestBridge.vertexEquiv_symm_core_tail candidate.datum face.realization drop,
      ZeroForestBridge.vertexEquiv_symm_core_tail candidate.datum face.realization keep]
    exact congrArg Prod.fst hEnds
  · refine ZeroForestPreservation.sourceVertexOf_injective candidate.datum ?_
    rw [ZeroForestBridge.vertexEquiv_symm_core_head candidate.datum face.realization drop,
      ZeroForestBridge.vertexEquiv_symm_core_head candidate.datum face.realization keep]
    exact congrArg Prod.snd hEnds

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- **The necessary condition the receipt imposes on the local source.**
Contrapositive of `not_isForest_sourceZeroSet_of_parallel`: whoever supplies the
receipt must in particular guarantee that distinct vanishing source occurrences
join distinct pairs of quotient-source vertices. -/
theorem injOn_sourceEnds_of_isForest
    (face : Candidate.ClearedFace candidate presentation x)
    (hForest : IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      face.realization.sourceZeroSet) :
    ∀ slot ∈ face.realization.sourceZeroSet,
      ∀ slot' ∈ face.realization.sourceZeroSet,
        candidate.datum.sourceEnds (face.realization.sourceEdgeAt slot) =
            candidate.datum.sourceEnds (face.realization.sourceEdgeAt slot') →
          slot = slot' := by
  intro slot hSlot slot' hSlot' hEnds
  by_contra hNe
  exact not_isForest_sourceZeroSet_of_parallel face (Ne.symm hNe) hSlot' hSlot
    hEnds hForest

/-! ### The arithmetic constraint a length-matrix row imposes

`Candidate.ClearedFace.sourcePathLength_eq_scale_mul` says the cleared source
lengths along the displayed row `row` sum to `scale * (matrix ⬝ x) row`.  So a
row whose matrix value is nonzero cannot be swallowed by the zero set.  This is
the half of the honest Draisma--Vargas acyclicity argument that costs
nothing. -/

/-- A row of the length matrix with nonzero value at `x` carries a source
occurrence of nonzero cleared length. -/
theorem exists_sourceLength_ne_zero_of_mulVec_ne_zero
    (face : Candidate.ClearedFace candidate presentation x) {row : coordinate}
    (hRow : (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec x row ≠ 0) :
    ∃ edge ∈ presentation.path row, face.realization.sourceLength edge ≠ 0 := by
  by_contra hContra
  have hAll : ∀ edge ∈ presentation.path row,
      face.realization.sourceLength edge = 0 := by
    intro edge hEdge
    by_contra hLength
    exact hContra ⟨edge, hEdge, hLength⟩
  have hSum := face.sourcePathLength_eq_scale_mul row
  have hZero : ((presentation.path row).map
      (fun edge ↦ (face.realization.sourceLength edge : ℚ))).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro value hValue
    obtain ⟨edge, hEdge, rfl⟩ := List.mem_map.mp hValue
    rw [hAll edge hEdge]
    norm_num
  rw [hZero] at hSum
  have hScale : (face.scale : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr face.scale_pos.ne'
  exact (mul_ne_zero hScale hRow) hSum.symm

/-- The same, as a canonical quotient-source slot outside the zero set. -/
theorem exists_notMem_sourceZeroSet_of_mulVec_ne_zero
    (face : Candidate.ClearedFace candidate presentation x) {row : coordinate}
    (hRow : (GluingDatum.LengthMatrixPresentation.matrix presentation).mulVec x row ≠ 0) :
    ∃ slot : Fin candidate.datum.sourceGraph.edges.card,
      slot ∉ face.realization.sourceZeroSet ∧
        face.realization.sourceEdgeAt slot ∈ presentation.path row := by
  obtain ⟨edge, hEdge, hLength⟩ :=
    exists_sourceLength_ne_zero_of_mulVec_ne_zero face hRow
  refine ⟨face.realization.sourceSlotEquiv.symm edge, ?_, ?_⟩
  · rw [GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet,
      ← GluingDatum.NonnegativeIntegralRealization.sourceSlotEquiv_apply,
      Equiv.apply_symm_apply]
    exact hLength
  · rw [← GluingDatum.NonnegativeIntegralRealization.sourceSlotEquiv_apply,
      Equiv.apply_symm_apply]
    exact hEdge

end Face

/-! ## 3.  At a terminal march state

Everything above is now read at `ZeroFreeTerminalFace.clearedFaceOfTerminal`,
the cleared face of a terminal state. -/

section Terminal

variable {coordinate chart : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ}
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- **The weakest form of route 1.**  A nonnegative comparison vector `y` whose
vanishing columns contain those of the endpoint, and whose own cleared face is a
census forest, supplies the terminal receipt.  Taking `y` strictly positive
forces the endpoint to be zero-free and recovers the zero-free case
`isForest_of_currentFinish_ne_zero`; this is the precise sense
in which a route-1 argument must exhibit a *superset* of the vanishing columns
whose slot fibre is already known acyclic. -/
theorem isForest_of_currentFinish_zero_imp
    {state : State degree matrix baseStart baseFinish}
    (hTerminal : state.Terminal)
    {target : CFGraph.{0}} {data : GluingDatum target degree} {wall : target.V}
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    {y : coordinate → ℚ} (hNonnegative : ∀ column, 0 ≤ y column)
    (hImp : ∀ column, state.toMatrixState.currentFinish column = 0 → y column = 0)
    (hForest : IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      (Candidate.clearedFace candidate presentation y
        hNonnegative).realization.sourceZeroSet) :
    IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      (ZeroFreeTerminalFace.clearedFaceOfTerminal hTerminal candidate
        presentation).realization.sourceZeroSet :=
  isForest_of_zero_imp _ _ hImp hForest

/-- The zero-free case, rederived from `isForest_of_currentFinish_zero_imp`
with the constant comparison vector `1`.  It is exactly the instance in which
the superset of vanishing columns is empty. -/
theorem isForest_of_currentFinish_ne_zero
    {state : State degree matrix baseStart baseFinish}
    (hTerminal : state.Terminal)
    (hNonzero : ∀ column, state.toMatrixState.currentFinish column ≠ 0)
    {target : CFGraph.{0}} {data : GluingDatum target degree} {wall : target.V}
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate) :
    IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      (ZeroFreeTerminalFace.clearedFaceOfTerminal hTerminal candidate
        presentation).realization.sourceZeroSet := by
  have hNonnegative : ∀ column : coordinate, (0 : ℚ) ≤ 1 := fun _ ↦ zero_le_one
  refine isForest_of_currentFinish_zero_imp hTerminal candidate presentation
    hNonnegative (fun column hColumn ↦ absurd hColumn (hNonzero column)) ?_
  exact ZeroFreeTerminalFace.isForest_of_sourceZeroSet_empty _
    (ZeroFreeTerminalFace.sourceZeroSet_eq_empty_of_pos _ fun _ ↦ zero_lt_one)

/-- **What the march supplies for free.**  `currentFinish_map` identifies the
length-matrix image of the endpoint with the fixed vector `baseFinish`, so every
row with `baseFinish row ≠ 0` carries a source occurrence of nonzero cleared
length: no displayed row of the presentation is swallowed by the zero set.  No
new field of the march state is used — only `currentFinish_map`, which
`FiniteAtlasMarch.State` already carries, and the chart-matrix identification
the terminal face already has. -/
theorem exists_sourceLength_ne_zero_of_baseFinish_ne_zero
    {state : State degree matrix baseStart baseFinish}
    (hTerminal : state.Terminal)
    {target : CFGraph.{0}} {data : GluingDatum target degree} {wall : target.V}
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix presentation =
      matrix state.toMatrixState.label)
    {row : coordinate} (hRow : baseFinish row ≠ 0) :
    ∃ edge ∈ presentation.path row,
      (ZeroFreeTerminalFace.clearedFaceOfTerminal hTerminal candidate
        presentation).realization.sourceLength edge ≠ 0 := by
  refine exists_sourceLength_ne_zero_of_mulVec_ne_zero _ ?_
  rw [hMatrix, congrFun state.toMatrixState.currentFinish_map row]
  exact hRow

/-- The slot form: every row with `baseFinish row ≠ 0` displays a slot outside
the terminal zero set. -/
theorem exists_notMem_sourceZeroSet_of_baseFinish_ne_zero
    {state : State degree matrix baseStart baseFinish}
    (hTerminal : state.Terminal)
    {target : CFGraph.{0}} {data : GluingDatum target degree} {wall : target.V}
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix presentation =
      matrix state.toMatrixState.label)
    {row : coordinate} (hRow : baseFinish row ≠ 0) :
    ∃ slot : Fin candidate.datum.sourceGraph.edges.card,
      slot ∉ (ZeroFreeTerminalFace.clearedFaceOfTerminal hTerminal candidate
          presentation).realization.sourceZeroSet ∧
        (ZeroFreeTerminalFace.clearedFaceOfTerminal hTerminal candidate
          presentation).realization.sourceEdgeAt slot ∈ presentation.path row := by
  refine exists_notMem_sourceZeroSet_of_mulVec_ne_zero _ ?_
  rw [hMatrix, congrFun state.toMatrixState.currentFinish_map row]
  exact hRow

end Terminal

/-! ## 4.  The field route 2 would need, stated but not added

`SemanticAtlasMarch.State` does not carry this field.  The statement below is
the field a state would have to carry if the receipt were to be propagated
along the march instead of produced at the endpoint, written so that it makes
sense at **every** state: it mentions no face, hence no nonnegativity of the
endpoint.  `zeroFibreForest_iff_isForest` shows that at a terminal state it is
literally the forest receipt, so nothing is lost by this reformulation.

Concretely, the field would read

```
zeroFibre : ∀ (target : CFGraph.{0}) (data : GluingDatum target degree)
  (wall : target.V) (candidate : Candidate target degree data wall)
  (presentation : candidate.datum.LengthMatrixPresentation coordinate),
  GluingDatum.LengthMatrixPresentation.matrix presentation =
      matrix toMatrixState.label →
    ZeroFibreForest candidate.datum presentation toMatrixState.currentFinish
```

on `SemanticAtlasMarch.State` (or, equivalently, one more conjunct of
`CarriesClearedPencil` at `currentFinish` rather than `currentStart`).  §2
above is the reason not to add it: `not_isForest_sourceZeroSet_of_parallel`
exhibits faces at which the conjunct is false, so the field would have to be
*established* at the seed and *preserved* by every step — and the only thing
that can establish it is a statement about the source over the vanishing
columns, i.e. the local-source obligation of route 3. -/

section Field

variable {target : CFGraph} {degree : ℕ}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The census forest condition for the slot fibre of the vanishing columns of
`x`.  Stated without a cleared face, hence available at every march state. -/
def ZeroFibreForest (data : GluingDatum target degree)
    (presentation : data.LengthMatrixPresentation coordinate)
    (x : coordinate → ℚ) : Prop :=
  IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
    (slotsOver data presentation (zeroColumns x))

end Field

section FieldFace

variable {target : CFGraph.{0}} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {presentation : candidate.datum.LengthMatrixPresentation coordinate}
  {x : coordinate → ℚ}

/-- At any cleared face the face-free condition is the receipt itself. -/
theorem zeroFibreForest_iff_isForest
    (face : Candidate.ClearedFace candidate presentation x) :
    ZeroFibreForest candidate.datum presentation x ↔
      IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
        face.realization.sourceZeroSet := by
  rw [ZeroFibreForest, sourceZeroSet_eq_slotsOver face]

end FieldFace

section FieldTerminal

variable {coordinate chart : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ}
  {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- The hypothetical march field discharges the forest receipt. -/
theorem isForest_of_zeroFibreForest
    {state : State degree matrix baseStart baseFinish}
    (hTerminal : state.Terminal)
    {target : CFGraph.{0}} {data : GluingDatum target degree} {wall : target.V}
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (hFibre : ZeroFibreForest candidate.datum presentation
      state.toMatrixState.currentFinish) :
    IsForest (UnitSubdivisionPresentation.core candidate.datum.sourceGraph)
      (ZeroFreeTerminalFace.clearedFaceOfTerminal hTerminal candidate
        presentation).realization.sourceZeroSet :=
  (zeroFibreForest_iff_isForest _).mp hFibre

end FieldTerminal

end DraismaVargas.LocalCases.TerminalForestReceipt
