module

public import DraismaVargasCount.CanonicalSurvivor
public import DraismaVargasCount.PendantDivisorTransport
public import DraismaVargasCount.SurvivingSlotMap

@[expose] public section

/-!
# Placing a member on a target subdivision it only partly fills

This is a step of the endgame (step 5 of `Assembly`): from a `Closed`
odd-multiplicity member over `D.bigCore` at the **degenerate** request, produce the
big-side divisor that `ExpansionSeriesMoment.bnExists_of_bigDivisor` consumes.

## Why the construction at a positive request cannot be re-used verbatim

At a positive request the divisor is a literal pushforward of the member's
original pullback fibre along the surviving-vertex map, and the modules it uses
(`RowSlotMap`, `SurvivingSlotMap`, `CanonicalSurvivor.member_surviving_nonempty`)
are stated for

    member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree

with the divisor landing on `spec.scale (memberScale member)`.  At the
degenerate request that object does not exist: the request is `0` on the
contracted (forest) slots, `Spec.length_pos` forbids a `Spec` with a zero slot,
and `D.bigSpec` is a genuine `Spec` only because it gives a contracted slot
length **one**.  The `length_pos` obstruction thus bites from both ends.

## What this file does instead

It keeps the target `Spec` and the request apart.  The data is

* a target specification `B : Spec N Q` — in the application
  `B = D.bigSpec (small.scale k hk) hN hL`;
* a **natural-number** request `y : Fin Q → ℕ` — in the application the
  degenerate one, zero on the contracted slots;
* a member over `B.core` at `y`, closed, with realization scale
  `k = memberScale member`;
* the **fit** hypothesis `hFit : ∀ e, memberScale member * y e ≤ B.length e`:
  the member's realized length of a slot never overruns the room `B` gives it.

Nothing asks for equality.  On a slot where the member is short — a contracted
slot, realized length `0` against `B.length e = 1` — the whole row is pushed to
one end of `B`'s slot, which is exactly the forest contraction.  On a slot where
the member fills `B` exactly the placement is the one of `RowSlotMap`.

## What is proved

* `endpoints`, `reverse`, `reverse_endpoints` — the orientation of a row against
  its slot.  These are `RowSlotOrientation.member_endpoints` and
  `memberReverse_endpoints` with the *request* dropped from the statement: the
  proofs there never look at it, only at `member.ident` and looplessness of the
  core.
* `offsetVal`, `position`, `point` — the placement of the `j`-th vertex of a row
  on its slot of `B`, oriented by `reverse`.
* `survivingPoint`, `sourcePoint`, `divisor` — the same three-step construction
  as at a positive request (`SurvivingSlotMap`): branch vertices go to their core
  labels, surviving divalent vertices to their row addresses, everything else
  through `CanonicalSurvivor.representative`.
* `divisor_effective`, `divisor_degree` — effectivity and total degree, from
  `PendantDivisorTransport` and `GluingDatum.sum_sourceVertex_localDegree_over`.
* `sourcePoint_eq_interior_iff` — the fibre of the placement over an interior
  vertex of `B` is exactly the retraction class of the row occurrences that land
  there.  This is the one step the degenerate case makes new: a slot that the
  member does not fill has **no** interior vertices in `B` to reach.
* `divisor_interior` — hence the coefficient at an interior vertex is a literal
  `RowRealizedPosition.collisionCoefficient`.
* `divisor_interior_mem` — and therefore carries the odd-denominator receipt,
  which is `bnExists_of_bigDivisor`'s `hBig` verbatim.  The exactness hypothesis
  `hExact` is needed only on slots that *have* an interior vertex.

## What is NOT proved

* **Nothing here about rank.**  `divisor` is a pushforward along a map that
  collapses slots the member does not fill, and no statement below says rank
  survives that collapse.  That is stated as a named hypothesis in
  `DegenerateBigDivisor`.
* **No member is produced.**  Every statement takes the member as given.
* The placement is *not* claimed to be a graph morphism, and no statement below
  needs it to be: `PendantDivisorTransport.push` is a pushforward along a bare
  function, and `push_effective`/`push_degree` hold for any function.
-/

namespace DraismaVargas.Count.DegeneratePlacement

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableGraphIncidence StablePathCount
open CanonicalSurvivor PendantRetraction RowRealizedPosition
open RowWalk RowPosition RowSlotOrientation SurvivingSlotMap SlotMoment
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph.{0}} {degree : ℕ}

/-! ## 1.  Orientation, with the request dropped from the statement -/

section Orientation

variable {n p : ℕ} {core : Core n p} {request : Fin p → ℚ}

/-- **`RowSlotOrientation.member_endpoints`, request-free.**  The two branch
labels of an actual row are the two labels of its slot, in one of the two
orders.  The proof there reads only `member.ident` and looplessness of the
core; the requested lengths never enter, so nothing is assumed about them
here. -/
theorem endpoints (hLoopless : ∀ e : Fin p, core.tail e ≠ core.head e)
    (member : FibreMember core request degree) (slot : Fin p) :
    (member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot)) =
        core.tail slot ∧
      member.ident.vertex (finishBranch member.fullDim (member.ident.row.symm slot)) =
        core.head slot) ∨
    (member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot)) =
        core.head slot ∧
      member.ident.vertex (finishBranch member.fullDim (member.ident.row.symm slot)) =
        core.tail slot) := by
  classical
  have hEndpoint (label : Fin n)
      (hLabel : label = core.tail slot ∨ label = core.head slot) :
      label = member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot)) ∨
      label = member.ident.vertex (finishBranch member.fullDim (member.ident.row.symm slot)) := by
    have hPos : 0 < incidenceCount member.data (member.ident.vertex.symm label).1
        (member.ident.row.symm slot) := by
      rw [member.ident.incidence, Equiv.apply_symm_apply]
      unfold coreIncidence
      rcases hLabel with rfl | rfl <;> split_ifs <;> omega
    obtain ⟨edge, hInc, hPath⟩ := (incidenceCount_pos_iff _ _ _).mp hPos
    rcases branch_incident_eq_endpoint member.fullDim (member.ident.row.symm slot)
        (member.ident.vertex.symm label) ⟨edge.2, hPath⟩ hInc with h | h
    · exact Or.inl (by simpa only [Equiv.apply_symm_apply] using congrArg member.ident.vertex h)
    · exact Or.inr (by simpa only [Equiv.apply_symm_apply] using congrArg member.ident.vertex h)
  have hTail := hEndpoint (core.tail slot) (Or.inl rfl)
  have hHead := hEndpoint (core.head slot) (Or.inr rfl)
  have hNe := hLoopless slot
  rcases hTail with hTail | hTail <;> rcases hHead with hHead | hHead
  · exact False.elim (hNe (hTail.trans hHead.symm))
  · exact Or.inl ⟨hTail.symm, hHead.symm⟩
  · exact Or.inr ⟨hHead.symm, hTail.symm⟩
  · exact False.elim (hNe (hTail.trans hHead.symm))

/-- **`RowSlotOrientation.memberReverse`, request-free.**  `true` when the
actual row runs against its slot's stored orientation. -/
noncomputable def reverse (member : FibreMember core request degree) (slot : Fin p) : Bool :=
  decide (member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot)) ≠
    core.tail slot)

theorem reverse_endpoints (hLoopless : ∀ e : Fin p, core.tail e ≠ core.head e)
    (member : FibreMember core request degree) (slot : Fin p) :
    member.ident.vertex (startBranch member.fullDim (member.ident.row.symm slot)) =
        (if reverse member slot then core.head slot else core.tail slot) ∧
    member.ident.vertex (finishBranch member.fullDim (member.ident.row.symm slot)) =
        (if reverse member slot then core.tail slot else core.head slot) := by
  classical
  rcases endpoints hLoopless member slot with ⟨hStart, hFinish⟩ | ⟨hStart, hFinish⟩
  · have hRev : reverse member slot = false := by
      unfold reverse
      exact decide_eq_false (not_not.mpr hStart)
    simp only [hRev, Bool.false_eq_true, ↓reduceIte, hStart, hFinish, and_self]
  · have hRev : reverse member slot = true := by
      unfold reverse
      exact decide_eq_true (by rw [hStart]; exact (hLoopless slot).symm)
    simp only [hRev, ↓reduceIte, hStart, hFinish, and_self]

end Orientation


/-! ## 2.  The placement of a member on a target it only partly fills -/

section Placement

variable {N Q : ℕ} (B : Spec N Q) (y : Fin Q → ℕ)
  (member : FibreMember B.core (fun e ↦ (y e : ℚ)) degree)
  (hClosed : member.Closed)

/-- **The base point for the pendant retraction.**  This is
`CanonicalSurvivor.member_surviving_nonempty` with the request dropped: the
proof there uses only `spec.core_nonempty` and the vertex dictionary. -/
theorem surviving_nonempty :
    ∃ vertex : member.data.SourceVertex, 0 < nonDanglingValency member.data vertex :=
  ⟨(member.ident.vertex.symm ⟨0, B.core_nonempty⟩).1,
    lt_of_lt_of_le (by decide : 0 < 3) (member.ident.vertex.symm ⟨0, B.core_nonempty⟩).2⟩

variable (hFit : ∀ e : Fin Q, memberScale member * y e ≤ B.length e)

include hFit in
theorem integralPrefix_le (e : Fin Q) (j : ℕ) :
    integralPrefix member.fullDim (memberRealization member hClosed)
      (member.ident.row.symm e) j ≤ B.length e := by
  have hLe := RowSlotMap.integralPrefix_le_full member.fullDim
    (memberRealization member hClosed) (member.ident.row.symm e) j
  rw [member_integralPrefix_full y member hClosed e] at hLe
  exact hLe.trans (hFit e)

/-- The integral distance from the slot's **tail** at which the `j`-th vertex of
the actual row of `e` is placed.  On a slot the member fills exactly this is
`RowSlotMap.rowOffset`; on a slot it does not fill, the row is pushed to the
end of `B`'s slot that the row starts from. -/
noncomputable def offsetVal (e : Fin Q) (j : ℕ) : ℕ :=
  if reverse member e then
    B.length e - integralPrefix member.fullDim (memberRealization member hClosed)
      (member.ident.row.symm e) j
  else
    integralPrefix member.fullDim (memberRealization member hClosed)
      (member.ident.row.symm e) j

include hFit in
theorem offsetVal_le (e : Fin Q) (j : ℕ) : offsetVal B y member hClosed e j ≤ B.length e := by
  have := integralPrefix_le B y member hClosed hFit e j
  unfold offsetVal
  split_ifs <;> omega

/-- The placement as a path position of `B`. -/
noncomputable def position (e : Fin Q) (j : ℕ) : B.PathPosition e :=
  ⟨offsetVal B y member hClosed e j, by
    have := offsetVal_le B y member hClosed hFit e j
    omega⟩

@[simp] theorem position_val (e : Fin Q) (j : ℕ) :
    (position B y member hClosed hFit e j).val = offsetVal B y member hClosed e j := rfl

/-- The placement as a vertex of `B`. -/
noncomputable def point (e : Fin Q) (j : ℕ) : B.Vertex :=
  B.pathVertex e (position B y member hClosed hFit e j)

end Placement


/-! ## 3.  The divisor: a literal pushforward of the original pullback fibre -/

section Divisor

variable {N Q : ℕ} (B : Spec N Q) (y : Fin Q → ℕ)
  (member : FibreMember B.core (fun e ↦ (y e : ℚ)) degree)
  (hClosed : member.Closed)
  (hFit : ∀ e : Fin Q, memberScale member * y e ≤ B.length e)

/-- The image of one literal interior row address. -/
noncomputable def addressPoint (address : InteriorAddress member.fullDim) : B.Vertex :=
  point B y member hClosed hFit (member.ident.row address.1) (address.2.val + 1)

/-- **The map on surviving source vertices.**  Exactly the shape of
`SurvivingSlotMap.survivingPoint`: branch vertices keep the member's own core
labels, and every surviving divalent vertex uses its unique interior row
address. -/
noncomputable def survivingPoint
    (vertex : {v : member.data.SourceVertex // 0 < nonDanglingValency member.data v}) :
    B.Vertex := by
  classical
  exact if hBranch : 3 ≤ nonDanglingValency member.data vertex.1 then
    B.coreVertex (member.ident.vertex ⟨vertex.1, hBranch⟩)
  else
    addressPoint B y member hClosed hFit
      ((addressEquiv member.fullDim).symm ⟨vertex.1, by
        have hNotOne := NonDanglingValency.nonDanglingValency_ne_one member.data
          member.fullDim.connected vertex.1
        have := vertex.2
        omega⟩)

theorem survivingPoint_branch (branch : BranchVertex member.data) :
    survivingPoint B y member hClosed hFit ⟨branch.1, by have := branch.2; omega⟩ =
      B.coreVertex (member.ident.vertex branch) := by
  classical
  simp only [survivingPoint, dite_eq_left branch.2]
  rfl

theorem survivingPoint_address (address : InteriorAddress member.fullDim) :
    survivingPoint B y member hClosed hFit
      ⟨addressVertex member.fullDim address, by rw [addressVertex_valency]; omega⟩ =
        addressPoint B y member hClosed hFit address := by
  classical
  have hNotBranch : ¬ 3 ≤ nonDanglingValency member.data
      (addressVertex member.fullDim address) := by rw [addressVertex_valency]; omega
  rw [survivingPoint, dite_eq_right hNotBranch]
  congr 1
  exact (addressEquiv member.fullDim).symm_apply_apply address

/-- The map on **every** original source vertex, pendant vertices included. -/
noncomputable def sourcePoint (vertex : member.data.SourceVertex) : B.Vertex :=
  survivingPoint B y member hClosed hFit
    (representative member.fullDim.connected (surviving_nonempty B y member) vertex)

theorem sourcePoint_of_retract {first second : member.data.SourceVertex}
    (hEq : retractVertex first = retractVertex second) :
    sourcePoint B y member hClosed hFit first = sourcePoint B y member hClosed hFit second := by
  unfold sourcePoint
  refine congrArg _ (Subtype.ext ?_)
  exact congrArg Subtype.val
    ((representative_eq_iff member.fullDim.connected (surviving_nonempty B y member) first _).mpr
      (hEq.trans (representative_class member.fullDim.connected
        (surviving_nonempty B y member) second)))

theorem sourcePoint_survivor
    (vertex : {v : member.data.SourceVertex // 0 < nonDanglingValency member.data v}) :
    sourcePoint B y member hClosed hFit vertex.1 =
      survivingPoint B y member hClosed hFit vertex := by
  unfold sourcePoint
  rw [representative_fixes member.fullDim.connected (surviving_nonempty B y member) vertex]

/-- The literal original pullback-fibre weight over a target vertex. -/
noncomputable def fibre (root : member.target.V) : CFDiv member.data.sourceGraph :=
  fun vertex ↦ if vertex.1.1 = root then
    ((member.data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0

/-- **The big-side divisor.**  A genuine finite pushforward of the member's own
pullback fibre along the placement, with nothing chosen existentially. -/
noncomputable def divisor (root : member.target.V) : CFDiv B.graph :=
  PendantDivisorTransport.push (G := member.data.sourceGraph) (H := B.graph)
    (sourcePoint B y member hClosed hFit) (fibre B y member root)

theorem divisor_apply (root : member.target.V) (v : B.Vertex) :
    divisor B y member hClosed hFit root v =
      ∑ raw : member.data.SourceVertex,
        if sourcePoint B y member hClosed hFit raw = v then fibre B y member root raw else 0 := rfl

theorem divisor_effective (root : member.target.V) :
    effective (divisor B y member hClosed hFit root) := by
  apply PendantDivisorTransport.push_effective
  intro vertex
  unfold fibre
  split_ifs <;> positivity

theorem divisor_degree (root : member.target.V) :
    deg (divisor B y member hClosed hFit root) = (degree : ℤ) :=
  (PendantDivisorTransport.push_degree (G := member.data.sourceGraph) (H := B.graph)
    (sourcePoint B y member hClosed hFit) (fibre B y member root)).trans
      (member.data.sum_sourceVertex_localDegree_over root)

end Divisor


/-! ## 4.  The fibre of the placement over an interior vertex -/

section Interior

variable {N Q : ℕ} (B : Spec N Q)

/-- The path position `o + 1` is the interior vertex `o`. -/
theorem pathVertex_interior (e : Fin Q) (o : Fin (B.length e - 1)) :
    B.pathVertex e ⟨o.val + 1, by have := o.isLt; omega⟩ = B.interiorVertex e o := by
  have hbound := o.isLt
  have hInterior : B.IsInteriorPosition e ⟨o.val + 1, by omega⟩ := by
    refine ⟨?_, ?_⟩
    · show 0 < o.val + 1
      omega
    · show o.val + 1 < B.length e
      omega
  rw [B.pathVertex_eq_interiorVertex e _ hInterior]
  congr 1

theorem pathVertex_eq_interior_iff (e : Fin Q) (q : B.PathPosition e)
    (o : Fin (B.length e - 1)) :
    B.pathVertex e q = B.interiorVertex e o ↔ q.val = o.val + 1 := by
  rw [← pathVertex_interior B e o]
  constructor
  · intro h
    exact congrArg Fin.val (B.pathVertex_injective e h)
  · intro h
    congr 1
    exact Fin.ext h

/-- A path position of a **different** slot never reaches an interior vertex of
`e`.  This is what makes the fibre calculation below local to one row. -/
theorem slot_eq_of_pathVertex_eq_interior {e e' : Fin Q} {q : B.PathPosition e'}
    {o : Fin (B.length e - 1)} (h : B.pathVertex e' q = B.interiorVertex e o) : e' = e := by
  unfold Spec.pathVertex at h
  split_ifs at h
  · exact absurd h (by simp [Spec.coreVertex, Spec.interiorVertex])
  · exact absurd h (by simp [Spec.coreVertex, Spec.interiorVertex])
  · exact congrArg Sigma.fst (Sum.inr.inj h)

variable (y : Fin Q → ℕ)
  (member : FibreMember B.core (fun e ↦ (y e : ℚ)) degree)
  (hClosed : member.Closed)
  (hFit : ∀ e : Fin Q, memberScale member * y e ≤ B.length e)

/-- Every surviving source vertex is a branch vertex or an interior row
address.  This is the case split `SurvivingSlotMap.survivingPoint` is defined
by, made into a statement so that nothing below has to unfold it. -/
theorem survivor_cases
    (vertex : {v : member.data.SourceVertex // 0 < nonDanglingValency member.data v}) :
    (∃ b : BranchVertex member.data, vertex.1 = b.1) ∨
      (∃ a : InteriorAddress member.fullDim, vertex.1 = addressVertex member.fullDim a) := by
  by_cases hBranch : 3 ≤ nonDanglingValency member.data vertex.1
  · exact Or.inl ⟨⟨vertex.1, hBranch⟩, rfl⟩
  · have hNotOne := NonDanglingValency.nonDanglingValency_ne_one member.data
      member.fullDim.connected vertex.1
    have hTwo : nonDanglingValency member.data vertex.1 = 2 := by
      have := vertex.2
      omega
    obtain ⟨a, ha⟩ := exists_address member.fullDim vertex.1 hTwo
    exact Or.inr ⟨a, ha.symm⟩

/-- **The one new step.**  A source vertex is placed at the interior vertex `o`
of slot `e` exactly when its pendant-retraction class is that of a row
occurrence of `e` whose oriented offset is `o + 1`.  Nothing here asks the
member to fill `e`: a slot it does not fill has no interior vertex of `B` to
reach, and the statement is then empty on both sides. -/
theorem sourcePoint_eq_interior_iff (e : Fin Q) (o : Fin (B.length e - 1))
    (raw : member.data.SourceVertex) :
    sourcePoint B y member hClosed hFit raw = B.interiorVertex e o ↔
      ∃ i : Fin ((orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length - 1),
        retractVertex raw =
          retractVertex (rowVertex member.fullDim (member.ident.row.symm e) (i.val + 1)) ∧
        offsetVal B y member hClosed e (i.val + 1) = o.val + 1 := by
  classical
  constructor
  · intro h
    have hRep := representative_class member.fullDim.connected
      (surviving_nonempty B y member) raw
    rcases survivor_cases B y member (representative member.fullDim.connected
        (surviving_nonempty B y member) raw) with ⟨b, hb⟩ | ⟨a, ha⟩
    · have hCore : sourcePoint B y member hClosed hFit raw =
          B.coreVertex (member.ident.vertex b) := by
        have hEq : representative member.fullDim.connected
            (surviving_nonempty B y member) raw = ⟨b.1, by have := b.2; omega⟩ := Subtype.ext hb
        unfold sourcePoint
        rw [hEq, survivingPoint_branch]
      rw [hCore] at h
      exact absurd h (by simp [Spec.coreVertex, Spec.interiorVertex])
    · have hAddr : sourcePoint B y member hClosed hFit raw =
          addressPoint B y member hClosed hFit a := by
        have hEq : representative member.fullDim.connected
            (surviving_nonempty B y member) raw =
            ⟨addressVertex member.fullDim a, by rw [addressVertex_valency]; omega⟩ :=
          Subtype.ext ha
        unfold sourcePoint
        rw [hEq, survivingPoint_address]
      rw [hAddr] at h
      obtain ⟨path, index⟩ := a
      simp only [addressPoint, point] at h
      have hSlot : member.ident.row path = e := slot_eq_of_pathVertex_eq_interior B h
      have hPath : path = member.ident.row.symm e := by
        rw [← hSlot, Equiv.symm_apply_apply]
      subst hPath
      refine ⟨index, hRep.trans (congrArg retractVertex ha), ?_⟩
      rw [Equiv.apply_symm_apply] at h
      exact (pathVertex_eq_interior_iff B e _ o).mp h
  · rintro ⟨i, hClass, hOffset⟩
    have hSurv : 0 < nonDanglingValency member.data (addressVertex member.fullDim
        (⟨member.ident.row.symm e, i⟩ : InteriorAddress member.fullDim)) := by
      have := addressVertex_valency member.fullDim
        (⟨member.ident.row.symm e, i⟩ : InteriorAddress member.fullDim)
      omega
    have hStep : sourcePoint B y member hClosed hFit
        (addressVertex member.fullDim (⟨member.ident.row.symm e, i⟩ :
          InteriorAddress member.fullDim)) =
        addressPoint B y member hClosed hFit ⟨member.ident.row.symm e, i⟩ :=
      (sourcePoint_survivor B y member hClosed hFit ⟨_, hSurv⟩).trans
        (survivingPoint_address B y member hClosed hFit _)
    calc sourcePoint B y member hClosed hFit raw
        = sourcePoint B y member hClosed hFit
            (addressVertex member.fullDim
              (⟨member.ident.row.symm e, i⟩ : InteriorAddress member.fullDim)) :=
          sourcePoint_of_retract B y member hClosed hFit hClass
      _ = addressPoint B y member hClosed hFit ⟨member.ident.row.symm e, i⟩ := hStep
      _ = B.interiorVertex e o := by
          show point B y member hClosed hFit (member.ident.row (member.ident.row.symm e))
            (i.val + 1) = B.interiorVertex e o
          rw [Equiv.apply_symm_apply]
          show B.pathVertex e (position B y member hClosed hFit e (i.val + 1)) = _
          rw [pathVertex_eq_interior_iff]
          exact hOffset

end Interior


/-! ## 5.  The interior coefficients, and their odd-denominator receipt -/

section Receipt

variable {N Q : ℕ} (B : Spec N Q) (y : Fin Q → ℕ)
  (member : FibreMember B.core (fun e ↦ (y e : ℚ)) degree)
  (hClosed : member.Closed)
  (hFit : ∀ e : Fin Q, memberScale member * y e ≤ B.length e)

include hFit in
theorem offsetVal_eq_iff (e : Fin Q) (o : Fin (B.length e - 1)) (j : ℕ) :
    offsetVal B y member hClosed e j = o.val + 1 ↔
      integralPrefix member.fullDim (memberRealization member hClosed)
          (member.ident.row.symm e) j =
        (if reverse member e then B.length e - (o.val + 1) else o.val + 1) := by
  have hPrefix := integralPrefix_le B y member hClosed hFit e j
  have hBound := o.isLt
  unfold offsetVal
  split_ifs <;> omega

/-- **The coefficient of the big-side divisor at an interior vertex** is a
literal `RowRealizedPosition.collisionCoefficient` of the member's own row, read
at the oriented offset.  No positivity of the request is used. -/
theorem divisor_interior (root : member.target.V) (e : Fin Q) (o : Fin (B.length e - 1)) :
    divisor B y member hClosed hFit root (B.interiorVertex e o) =
      collisionCoefficient member.fullDim (memberRealization member hClosed) root
        (member.ident.row.symm e)
        (if reverse member e then B.length e - (o.val + 1) else o.val + 1) := by
  classical
  rw [divisor_apply, RowVertexEnumeration.collisionCoefficient_eq_raw_fibre_sum]
  refine Finset.sum_congr rfl fun raw _ ↦ ?_
  have hCond : (sourcePoint B y member hClosed hFit raw = B.interiorVertex e o) ↔
      (∃ i : Fin ((orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length - 1),
        retractVertex raw =
            retractVertex (rowVertex member.fullDim (member.ident.row.symm e) (i.val + 1)) ∧
          integralPrefix member.fullDim (memberRealization member hClosed)
              (member.ident.row.symm e) (i.val + 1) =
            (if reverse member e then B.length e - (o.val + 1) else o.val + 1)) := by
    rw [sourcePoint_eq_interior_iff]
    exact exists_congr fun i ↦
      and_congr_right fun _ ↦ offsetVal_eq_iff B y member hClosed hFit e o (i.val + 1)
  by_cases hRoot : raw.1.1 = root
  · simp only [fibre, hRoot, ite_true, true_and]
    by_cases hHit : sourcePoint B y member hClosed hFit raw = B.interiorVertex e o
    · rw [ite_eq_left hHit, ite_eq_left (hCond.mp hHit)]
    · rw [ite_eq_right hHit, ite_eq_right fun hx ↦ hHit (hCond.mpr hx)]
  · simp only [fibre, hRoot, ite_false, false_and, ite_false, ite_self]

/-- **`bnExists_of_bigDivisor`'s `hBig`, at the placement.**  Every interior
coefficient carries the odd-denominator receipt at its own position.  The
exactness hypothesis is asked only where it can be used: a slot with an interior
vertex has length at least two, and is therefore one the member fills. -/
theorem divisor_interior_mem
    (hExact : ∀ e : Fin Q, 1 < B.length e → memberScale member * y e = B.length e)
    (hOdd : Odd member.oddMult) {root : member.target.V}
    (hInternal : ¬ IsLeafVertex member.target root)
    (e : Fin Q) (o : Fin (B.length e - 1)) :
    ((divisor B y member hClosed hFit root (B.interiorVertex e o) : ℤ) : ℚ) *
        (((o.val + 1 : ℕ) : ℚ) / (memberScale member : ℚ)) ∈ oddDenominatorSubring := by
  classical
  rw [divisor_interior]
  by_cases hRev : reverse member e = true
  · have hInner := o.isLt
    have hLength : memberScale member * y e = B.length e := hExact e (by omega)
    have hOff : B.length e - (o.val + 1) = memberScale member * y e - (o.val + 1) := by
      rw [hLength]
    simp only [hRev, ite_true, hOff]
    have hBound : o.val + 1 ≤ memberScale member * y e := by omega
    have hScaleQ : (memberScale member : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (memberScale_pos member))
    set c := collisionCoefficient member.fullDim (memberRealization member hClosed) root
      (member.ident.row.symm e) (memberScale member * y e - (o.val + 1)) with hc
    have hTerm := member_collisionCoefficient_mem (fun e ↦ ((y e : ℤ))) member hClosed hOdd e
      hInternal (memberScale member * y e - (o.val + 1))
    have hTotal : ((c : ℤ) : ℚ) * ((y e : ℕ) : ℚ) ∈ oddDenominatorSubring :=
      oddDenominatorSubring.mul_mem (intCast_mem _ c) (natCast_mem _ (y e))
    have hDifference := oddDenominatorSubring.sub_mem hTotal hTerm
    simp only [Nat.cast_sub hBound, Nat.cast_mul] at hDifference
    convert hDifference using 1
    field_simp
    ring
  · simp only [hRev, Bool.false_eq_true, ite_false]
    exact member_collisionCoefficient_mem (fun e ↦ ((y e : ℤ))) member hClosed hOdd e
      hInternal (o.val + 1)

end Receipt

end DraismaVargas.Count.DegeneratePlacement
