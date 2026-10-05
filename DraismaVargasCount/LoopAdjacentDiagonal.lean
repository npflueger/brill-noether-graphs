module

public import DraismaVargasCount.ExtractGenusTwo
public import DraismaVargasCount.BallotOrbitStability

@[expose] public section

/-!
# A diagonal member is pinned on every loop-adjacent slot

**Source.**  Vargas, Part II (arXiv:2609.09109), part (1) of `prop-caterpillar-ballot` (the
slopes on the path edges), in its geometric form: the core diagonal of a diagonal member.

## What this sharpens

`Count/ExtractGenusTwo.lean` proves two facts about a **diagonal** member, both at every
genus and over every core:

* `coreDiag_eq_two_of_loop` -- it reads `2` at every self-loop slot;
* `exists_coreDiag_eq_half_of_loop` -- each self-loop slot supplies *a* slot
  reading `1 / 2`, namely the slot of the stable row carrying that lollipop's
  bridge occurrence.

At `m = 0` the second one pins the whole core diagonal, because `Fin 3` has only one
non-leaf slot.  At `m ≥ 1` one needs to know which slot carries the `1 / 2`.

**That identification is available, at every `m`.**  The bridge occurrence is
incident to the lollipop branch vertex `A`, and `A` is by definition the branch
vertex `member.ident.vertex.symm (core.tail slot)` sitting over the loop's core
vertex, so `member.ident.incidence` puts the bridge's row **at that core
vertex**: §1 strengthens `exists_coreDiag_eq_half_of_loop` to report
`0 < coreIncidence core (core.tail slot) stem`.  Over `catCore m` a loop vertex
carries exactly one slot besides its loop (§2, arithmetic in the raw indices),
so the `1 / 2` is pinned on the nose.

The consequence (§3) is that a diagonal member's core diagonal is **determined
on every loop-adjacent slot**, in the sense of `Count.BallotOrbit.LoopAdjacent` (the slot
has an endpoint carrying a self-loop).  That is `4m + 4` of the `6m + 3` slots -- the
`2m + 2` loops, the `2m` stems and the two extreme spine slots -- and on all of them the
value agrees with **every** ballot diagonal, by
`BallotOrbit.ballotCoreDiag_of_loopAdjacent`.

So the `extract` field of `BallotSlopes.DiagonalClassification` is exactly its
restriction to the `2m - 1` **interior spine slots**.  At genus six that is
three slots, `4`, `7` and `10`, against the nine that
`ExtractGenusTwo.diagonalExtract_iff_forall_not_isLeafEdge` leaves.  This is the
same `4m + 4` / `2m - 1` split that carries the orbit theorem of
`BallotOrbitStability`, on the geometric side rather than the ballot side.

## What is proved

* `exists_coreIncidence_pos_coreDiag_eq_half_of_loop` -- **at every genus and
  over every core**, the `1 / 2` a self-loop supplies sits on a slot *incident
  to the loop's own core vertex*.  This is
  `ExtractGenusTwo.exists_coreDiag_eq_half_of_loop` with the location added;
  the proof is that one with the `member.ident.incidence` step appended.
* `catTailVal_of_isLeafEdge`, `incident_loopVertex_eq`,
  `eq_of_incident_loopVertex` -- **a loop vertex of `catCore m` carries exactly
  one slot besides its loop**, and that slot is `t - 1`, or `1` when the loop
  is slot `0`.
* `coreDiag_eq_half_of_loopAdjacent` -- **the pin**: a diagonal member reads
  `1 / 2` at every loop-adjacent non-leaf slot of `catCore m`, at every `m`,
  with no request hypothesis, no `Open` and no `HasOddMult`.
* `coreDiag_apply_of_loopAdjacent`, `coreDiag_eq_ballotCoreDiag_of_loopAdjacent`
  -- the value in closed form, and its agreement with every ballot diagonal.
* `diagonalExtract_of_forall_not_loopAdjacent`,
  **`diagonalExtract_iff_forall_not_loopAdjacent`** -- the `extract` field
  **is** its restriction to the `2m - 1` non-loop-adjacent slots.
* `diagonalExtract_genusTwo'` -- at `m = 0` there are none, so `extract` is
  free; this reproves `ExtractGenusTwo.diagonalExtract_genusTwo` by the general
  mechanism rather than by a `Fin 3` count, which is the check that the
  mechanism is the right one.

## What is not proved here

* **Nothing about the interior spine slots.**  `extract` at `m ≥ 1` is exactly
  the statement that the `2m - 1` values `mem.coreDiag (3i + 4)` are
  `1 / s_{i+2}` for a *single* slope sequence `s` -- the reciprocals of a ballot
  sequence, in order.  This module does not touch it; at genus six it is three rational
  numbers and five admissible triples.
* **`Diagonal` is essential.**  Every statement below assumes it;
  `Count.ColumnTwist.not_forall_extract` shows that `extract` over all members, not only
  the diagonal ones, fails.
* `Open` and `HasOddMult` are not used below, so the pin is stronger than the
  `extract` field needs.  That is not evidence they are removable from what is
  left.
* Nothing here constructs a member, bears on the `diagonal` or `rigid` fields,
  on parity, or on `CaterpillarBallot.BallotFamily`.
-/

namespace DraismaVargas.Count.LoopAdjacentDiagonal

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount incidenceCount_pos_iff)
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.BallotOrbit (LoopVertex LoopAdjacent)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  The `1 / 2` is located at the loop's core vertex -/

section Located

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **`ExtractGenusTwo.exists_coreDiag_eq_half_of_loop`, with the location.**

At every genus and over every core, the slot on which a self-loop's bridge
occurrence puts the value `1 / 2` is *incident to the loop's own core vertex*.

The proof is that of `ExtractGenusTwo.exists_coreDiag_eq_half_of_loop`, with one step
added at the end: the bridge is incident
to `LollipopDivalent.loopBranch member hLoop`, which **is** the branch vertex
`member.ident.vertex.symm (core.tail slot)`, so `member.ident.incidence` turns
the positive stable-path incidence count at that branch vertex into a positive
`coreIncidence` at `core.tail slot`. -/
theorem exists_coreIncidence_pos_coreDiag_eq_half_of_loop
    (member : FibreMember core y degree) (hD : member.Diagonal)
    {slot : Fin p} (hLoop : core.tail slot = core.head slot) :
    ∃ stem : Fin p, stem ≠ slot ∧
      0 < coreIncidence core (core.tail slot) stem ∧ member.coreDiag stem = 1 / 2 := by
  classical
  obtain ⟨bridge, hSurv, hInc, _hOff, hIdx⟩ :=
    LollipopBridgeFibreWitness.exists_bridge_loopBranch member hLoop
  set r := member.fullDim.labelling.row
    (NonDanglingEdge.stablePath (⟨bridge, hSurv⟩ : NonDanglingEdge member.data)) with hr
  have hmem : bridge ∈ EdgeDenominator.rowEdges member.fullDim.labelling r :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨hSurv, rfl⟩
  have hSupport : ∀ j, j ≠ r → GluingDatum.LengthMatrixPresentation.matrix
      member.fullDim.labelling.presentation r j = 0 := fun j hj ↦ hD r j hj
  have hTarget : bridge.1.1 = member.fullDim.labelling.targetEdge r :=
    NonTrivalentCorner.target_eq_of_supported member.fullDim.labelling hSupport hmem
  have hNonleaf : r ∉ leafColumns member.fullDim.labelling.presentation := by
    intro hcol
    obtain ⟨v, hv, hincid⟩ := (mem_leafColumns _ _).mp hcol
    have hleafedge : bridge.1.1 = leafEdge hv := by
      rw [hTarget]; exact eq_leafEdge_of_mem hv hincid
    have hone := LeafFibre.sourceEdgeIndex_eq_one_above_leaf member.fullDim hv hleafedge
    omega
  obtain ⟨e, _he, hfibre, hval⟩ :=
    NonTrivalentCorner.corner_eq_reciprocal_of_nonleaf member.fullDim hSupport hNonleaf
  have hbf : bridge ∈ LeafFibre.rowFibre member.fullDim.labelling r
      (member.fullDim.labelling.targetEdge r) :=
    (EdgeDenominator.mem_rowFibre_iff _ _ _ _).mpr ⟨hmem, hTarget⟩
  rw [hfibre, Finset.mem_singleton] at hbf
  have hhalf : member.coreDiag (member.slotMap r) = 1 / 2 := by
    have hsymm : member.slotMap.symm (member.slotMap r) = r := member.slotMap.symm_apply_apply r
    show GluingDatum.LengthMatrixPresentation.matrix member.fullDim.labelling.presentation
      (member.slotMap.symm (member.slotMap r)) (member.slotMap.symm (member.slotMap r)) = 1 / 2
    rw [hsymm, hval, ← hbf, hIdx]
    norm_num
  have hpos : 0 < incidenceCount member.data
      (LollipopDivalent.loopBranch member hLoop)
      (member.ident.row.symm (member.slotMap r)) := by
    have hrow : member.ident.row.symm (member.slotMap r) =
        NonDanglingEdge.stablePath (⟨bridge, hSurv⟩ : NonDanglingEdge member.data) := by
      show member.ident.row.symm (member.ident.row
        (member.fullDim.labelling.row.symm r)) = _
      rw [Equiv.symm_apply_apply, hr, Equiv.symm_apply_apply]
    rw [hrow]
    exact (incidenceCount_pos_iff _ _ _).mpr
      ⟨(⟨bridge, hSurv⟩ : NonDanglingEdge member.data), hInc, rfl⟩
  have hincidence := member.ident.incidence
    (member.ident.vertex.symm (core.tail slot)) (member.slotMap r)
  rw [Equiv.apply_symm_apply] at hincidence
  refine ⟨member.slotMap r, ?_, ?_, hhalf⟩
  · rintro rfl
    rw [ExtractGenusTwo.coreDiag_eq_two_of_loop member hD hLoop] at hhalf
    norm_num at hhalf
  · rw [← hincidence]
    exact hpos

end Located

/-! ## 2.  A loop vertex of `catCore m` carries one slot besides its loop -/

section CatCore

open DraismaVargas.Count.SlopeRigidity (catCore_tail_val coreIncidence_catCore_val
  catCore_tail_eq_head_iff)
open DraismaVargas.Infrastructure.CaterpillarTree (parentIndex)

variable {m : ℕ}

/-- A self-loop slot of `catCore m` is its own parent index. -/
theorem catTailVal_of_isLeafEdge (m : ℕ) {t : Fin (6 * m + 3)} (ht : IsLeafEdge m t) :
    catTailVal m t = t.val := by
  have h1 := t.isLt
  have ht' : t.val % 3 = 0 ∨ t.val = 6 * m + 2 := ht
  unfold catTailVal parentIndex
  split_ifs <;> omega

/-- **The slot at a loop vertex, named.**  A slot other than the loop `t` and
incident to the loop's vertex is `t - 1`, or slot `1` when `t` is slot `0`.
At genus six: the loops `0, 3, 6, 9, 12, 14` are matched with `1, 2, 5, 8, 11,
13`, which are the two extreme spine slots and the four stems. -/
theorem incident_loopVertex_eq (m : ℕ) {t e : Fin (6 * m + 3)} (ht : IsLeafEdge m t)
    (he : e ≠ t) (hi : 0 < coreIncidence (catCore m) ((catCore m).tail t) e) :
    e.val = if t.val = 0 then 1 else t.val - 1 := by
  have h1 := t.isLt
  have h2 := e.isLt
  have ht' : t.val % 3 = 0 ∨ t.val = 6 * m + 2 := ht
  have hne : e.val ≠ t.val := fun h ↦ he (Fin.ext h)
  rw [coreIncidence_catCore_val, catCore_tail_val, catTailVal_of_isLeafEdge m ht] at hi
  have hor : branchIdx (catTailVal m e) = branchIdx t.val ∨
      branchIdx (catHeadVal m e) = branchIdx t.val := by
    by_cases hA : branchIdx (catTailVal m e) = branchIdx t.val
    · exact Or.inl hA
    · refine Or.inr ?_
      rw [ite_eq_right hA] at hi
      by_contra hB
      rw [ite_eq_right hB] at hi
      omega
  unfold catTailVal catHeadVal branchIdx parentIndex IsLeafEdge at hor
  split_ifs at hor ⊢ <;> omega

/-- **Uniqueness.**  Two slots other than `t` incident to `t`'s loop vertex
coincide. -/
theorem eq_of_incident_loopVertex (m : ℕ) {t u u' : Fin (6 * m + 3)} (ht : IsLeafEdge m t)
    (hu : u ≠ t) (hu' : u' ≠ t)
    (hui : 0 < coreIncidence (catCore m) ((catCore m).tail t) u)
    (hu'i : 0 < coreIncidence (catCore m) ((catCore m).tail t) u') :
    u = u' :=
  Fin.ext ((incident_loopVertex_eq m ht hu hui).trans
    (incident_loopVertex_eq m ht hu' hu'i).symm)

end CatCore

/-! ## 3.  The core diagonal on the loop-adjacent slots -/

section Pin

open DraismaVargas.Count.SlopeRigidity (catCore_tail_eq_head_iff)

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-- **A diagonal member reads `1 / 2` at every loop-adjacent non-leaf slot of
`catCore m`, at every genus.**  No request hypothesis, no `Open`, no
`HasOddMult`. -/
theorem coreDiag_eq_half_of_loopAdjacent (member : FibreMember (catCore m) request (m + 2))
    (hD : member.Diagonal) {e : Fin (6 * m + 3)} (hAdj : LoopAdjacent (catCore m) e)
    (hLeaf : ¬ IsLeafEdge m e) :
    member.coreDiag e = 1 / 2 := by
  obtain ⟨t, htail, hhead⟩ : ∃ t : Fin (6 * m + 3),
      (catCore m).tail t = (catCore m).head t ∧
        0 < coreIncidence (catCore m) ((catCore m).tail t) e := by
    rcases hAdj with ⟨t, ht1, ht2⟩ | ⟨t, ht1, ht2⟩
    · refine ⟨t, ht1.trans ht2.symm, ?_⟩
      rw [coreIncidence, ite_eq_left ht1.symm]
      omega
    · refine ⟨t, ht1.trans ht2.symm, ?_⟩
      rw [coreIncidence,
        ite_eq_left (show (catCore m).head e = (catCore m).tail t from ht1.symm)]
      omega
  have htLeaf : IsLeafEdge m t := (catCore_tail_eq_head_iff m t).mp htail
  have hne : e ≠ t := fun h ↦ hLeaf (h ▸ htLeaf)
  obtain ⟨u, hu, hui, hhalf⟩ :=
    exists_coreIncidence_pos_coreDiag_eq_half_of_loop member hD htail
  rwa [eq_of_incident_loopVertex m htLeaf hu hne hui hhead] at hhalf

/-- The value in closed form on the loop-adjacent slots: `2` on a self-loop,
`1 / 2` on everything else that touches one. -/
theorem coreDiag_apply_of_loopAdjacent (member : FibreMember (catCore m) request (m + 2))
    (hD : member.Diagonal) {e : Fin (6 * m + 3)} (hAdj : LoopAdjacent (catCore m) e) :
    member.coreDiag e = if IsLeafEdge m e then 2 else 1 / 2 := by
  by_cases hLeaf : IsLeafEdge m e
  · rw [ite_eq_left hLeaf, ExtractGenusTwo.coreDiag_eq_two_of_isLeafEdge member hD hLeaf]
  · rw [ite_eq_right hLeaf, coreDiag_eq_half_of_loopAdjacent member hD hAdj hLeaf]

/-- **On the loop-adjacent slots a diagonal member already agrees with every
ballot diagonal.**  The ballot side is
`BallotOrbit.ballotCoreDiag_of_loopAdjacent`, the geometric side is §1--§2. -/
theorem coreDiag_eq_ballotCoreDiag_of_loopAdjacent
    (member : FibreMember (catCore m) request (m + 2)) (hD : member.Diagonal)
    (s : Slopes (2 * (m + 1))) {e : Fin (6 * m + 3)} (hAdj : LoopAdjacent (catCore m) e) :
    member.coreDiag e = BallotSlopes.ballotCoreDiag m s e := by
  rw [coreDiag_apply_of_loopAdjacent member hD hAdj,
    BallotOrbit.ballotCoreDiag_of_loopAdjacent m s hAdj]

/-- **`extract` reduces to the `2m - 1` interior spine slots, at every `m`.**
The `4m + 4` loop-adjacent slots are free by §1--§3.  At `m = 0` there are no
others, and at `m = 2` there are three. -/
theorem diagonalExtract_of_forall_not_loopAdjacent
    (h : ∀ member : FibreMember (catCore m) request (m + 2),
      member.Open → member.HasOddMult → member.Diagonal →
        ∃ s : Slopes (2 * (m + 1)), ∀ e : Fin (6 * m + 3), ¬ LoopAdjacent (catCore m) e →
          member.coreDiag e = BallotSlopes.ballotCoreDiag m s e) :
    BallotSlopes.DiagonalExtract m request := by
  intro member hOpen hOdd hD
  obtain ⟨s, hs⟩ := h member hOpen hOdd hD
  refine ⟨s, funext fun e ↦ ?_⟩
  by_cases hAdj : LoopAdjacent (catCore m) e
  · exact coreDiag_eq_ballotCoreDiag_of_loopAdjacent member hD s hAdj
  · exact hs e hAdj

/-- And the reduction loses nothing. -/
theorem diagonalExtract_iff_forall_not_loopAdjacent :
    BallotSlopes.DiagonalExtract m request ↔
      ∀ member : FibreMember (catCore m) request (m + 2),
        member.Open → member.HasOddMult → member.Diagonal →
          ∃ s : Slopes (2 * (m + 1)), ∀ e : Fin (6 * m + 3), ¬ LoopAdjacent (catCore m) e →
            member.coreDiag e = BallotSlopes.ballotCoreDiag m s e :=
  ⟨fun hextract member hOpen hOdd hD ↦ by
      obtain ⟨s, hs⟩ := hextract member hOpen hOdd hD
      exact ⟨s, fun e _ ↦ congrFun hs e⟩,
    diagonalExtract_of_forall_not_loopAdjacent⟩

/-- **Genus two, by the general mechanism.**  At `m = 0` every slot of
`catCore 0` is loop-adjacent (`BallotOrbit.not_loopAdjacent_catCore` asks for
`e % 3 = 1`, `e ≠ 1`, and `Fin 3` has no such slot), so `extract` is free.  This
is `ExtractGenusTwo.diagonalExtract_genusTwo` reproved without the `Fin 3`
count that located the `1 / 2` there. -/
theorem diagonalExtract_genusTwo' {request : Fin (6 * 0 + 3) → ℚ} :
    BallotSlopes.DiagonalExtract 0 request := by
  refine diagonalExtract_of_forall_not_loopAdjacent
    fun member _ _ _ ↦ ⟨BallotDatum.zig 0, fun e hAdj ↦ absurd ?_ hAdj⟩
  have he := e.isLt
  rw [BallotOrbit.loopAdjacent_catCore]
  omega

end Pin

end DraismaVargas.Count.LoopAdjacentDiagonal
