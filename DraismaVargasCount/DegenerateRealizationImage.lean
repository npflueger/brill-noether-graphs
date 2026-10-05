module

public import DraismaVargasCount.DegenerateFibreCover

@[expose] public section

/-!
# What the member's realization actually hits on the small subdivision

**Source.**  `DegenerateFibreCover` splits the rank hypothesis
`DegenerateBigDivisor.ForestContractionRank` of the specialisation step in the
endgame of the count (step 5 of `DraismaVargasCount/Assembly.lean`) into two
obligations and reduces the covering half to

    DegenerateFibreCover.RealizationSurjective :
      Function.Surjective (ExpansionData.vertexMap D (small.scale k hk) hN hL ∘
        DegeneratePlacement.sourcePoint …)

`DegenerateBigDivisor`'s header calls that composite "the member's own
realization" but does not compute it.  This file computes it, and turns the
surjectivity into a **checkable** condition on the member's own data.  The
computation of the image (the two families below) is what the endgame uses, in
`CorePencilCoverProducer` and `PencilTransportProducer`.

## What is proved

* `vertexMap_sourcePoint_branch` — a branch vertex of the member lands on the
  small core vertex `D.fib (member.ident.vertex branch)`.
* `vertexMap_sourcePoint_address` — an interior row address `a` lands on
  `kindVertex` of its big slot at the member's own oriented offset
  `DegeneratePlacement.offsetVal … (a.2.val + 1)`.  This is where the degenerate
  request shows: on a contracted slot `kindVertex` ignores the offset entirely
  and returns the fallback core vertex, which is exactly the forest contraction.
* `exists_realizedVertex_of_sourceVertex` — *every* source vertex lands in one of
  those two families, so the image of the realization is exactly their union.
* `realizationSurjective_iff` — hence `RealizationSurjective` is equivalent to the
  explicit condition `∀ b, RealizedVertex … b`: every vertex of the small
  subdivision is either a `D.fib`-image of a branch label or a `kindVertex` at a
  realized offset.

## Scope

* **`RealizedVertex` is not proved to hold.**  The iff is a restatement, not a
  discharge: `realizationSurjective_iff` moves the obligation from a `Surjective`
  about an opaque composite to a finite-looking disjunction, and stops there.
  (`DegenerateTransport` shows by counting that `RealizationSurjective` fails at
  every large enough scale.)
* Nor is `DegenerateFibreCover.FibreTransportFrom`, the other half of the
  split, proved here.
* Two remarks on `RealizedVertex`:
  - the branch family alone cannot suffice as soon as `D` has a `SlotKind.double`
    slot.  `ExpansionData.MarkerIsolated` says the middle vertex `small.core.head j₁`
    of such a slot is outside the image of `D.fib` altogether, so it can only be
    reached by the address family, at an offset equal to
    `(small.scale k hk).length j₁`.
  - a `SlotKind.contracted` big slot contributes exactly one small vertex no
    matter how many addresses it carries: `kindVertex` discards the offset on
    `.contracted` and returns the fallback core vertex.  So the address family
    is not "one small vertex per source vertex" either.

No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`.
-/

namespace DraismaVargas.Count.DegenerateRealizationImage

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableGraphIncidence
open DraismaVargas.Count.DegenerateBigDivisor
open DraismaVargas.Count.DegenerateFibreCover
open CanonicalSurvivor PendantRetraction RowRealizedPosition
open SurvivingSlotMap SlotMoment
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

variable {n p N Q degree : ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)

/-! ## 1.  The two families -/

/-- **A branch vertex of the member realizes a small core vertex.**  Its
placement is the big core vertex carrying its own core label, and the
contraction reads that off as `D.fib` of the label. -/
theorem vertexMap_sourcePoint_branch (branch : BranchVertex member.data) :
    ExpansionData.vertexMap D (small.scale k hk) hN hL
        (DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member hClosed
          (fit D small hN hL k hk member hScale) branch.1) =
      (small.scale k hk).coreVertex (D.fib (member.ident.vertex branch)) := by
  have hStep : DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
      (degenerateLength D small) member hClosed
      (fit D small hN hL k hk member hScale) branch.1 =
      (D.bigSpec (small.scale k hk) hN hL).coreVertex (member.ident.vertex branch) :=
    (DegeneratePlacement.sourcePoint_survivor (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale)
        ⟨branch.1, by have := branch.2; omega⟩).trans
      (DegeneratePlacement.survivingPoint_branch (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale)
        branch)
  rw [hStep]
  rfl

/-- **An interior row address realizes a `kindVertex` at its own offset.**  The
oriented offset is `DegeneratePlacement.offsetVal`, i.e. the member's own
integral prefix along the row, reflected when the row runs against the slot.

On a `SlotKind.contracted` big slot `kindVertex` discards the offset and returns
the fallback small core vertex: that is the forest contraction, visible here as
a statement rather than as a rank claim. -/
theorem vertexMap_sourcePoint_address (hCond : D.Conditions small.core)
    (address : InteriorAddress member.fullDim) :
    ExpansionData.vertexMap D (small.scale k hk) hN hL
        (DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member hClosed
          (fit D small hN hL k hk member hScale)
          (addressVertex member.fullDim address)) =
      kindVertex (small.scale k hk)
        (D.fib (D.bigCore.tail (member.ident.row address.1)))
        (D.kind (member.ident.row address.1))
        (DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member hClosed
          (member.ident.row address.1) (address.2.val + 1)) := by
  have hSurv : 0 < nonDanglingValency member.data (addressVertex member.fullDim address) := by
    have := addressVertex_valency member.fullDim address
    omega
  have hStep : DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
      (degenerateLength D small) member hClosed
      (fit D small hN hL k hk member hScale) (addressVertex member.fullDim address) =
      DegeneratePlacement.addressPoint (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed
        (fit D small hN hL k hk member hScale) address :=
    (DegeneratePlacement.sourcePoint_survivor (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale)
        ⟨addressVertex member.fullDim address, hSurv⟩).trans
      (DegeneratePlacement.survivingPoint_address (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale)
        address)
  rw [hStep]
  exact ExpansionData.vertexMap_pathVertex (D := D) (small := small.scale k hk)
    (hN := hN) (hL := hL) hCond (member.ident.row address.1)
    (DegeneratePlacement.position (D.bigSpec (small.scale k hk) hN hL)
      (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale)
      (member.ident.row address.1) (address.2.val + 1))

/-! ## 2.  The image, and the checkable form of the covering obligation -/

/-- **A vertex of the small subdivision the member's realization reaches.**  Either
it is the `D.fib`-image of one of the member's core labels, or it is the
`kindVertex` of some big slot at an offset the member actually realizes. -/
def RealizedVertex (b : (small.scale k hk).Vertex) : Prop :=
  (∃ branch : BranchVertex member.data,
      (small.scale k hk).coreVertex (D.fib (member.ident.vertex branch)) = b) ∨
    (∃ address : InteriorAddress member.fullDim,
      kindVertex (small.scale k hk)
          (D.fib (D.bigCore.tail (member.ident.row address.1)))
          (D.kind (member.ident.row address.1))
          (DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
            (degenerateLength D small) member hClosed
            (member.ident.row address.1) (address.2.val + 1)) = b)

/-- **Every source vertex realizes one of the two families.**  The pendant
retraction sends it to a surviving vertex, and `DegeneratePlacement.survivor_cases`
splits those into branch vertices and interior row addresses. -/
theorem exists_realizedVertex_of_sourceVertex (hCond : D.Conditions small.core)
    (raw : member.data.SourceVertex) :
    RealizedVertex D small hN hL k hk member hClosed
      (ExpansionData.vertexMap D (small.scale k hk) hN hL
        (DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member hClosed
          (fit D small hN hL k hk member hScale) raw)) := by
  classical
  have hEq : DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
      (degenerateLength D small) member hClosed
      (fit D small hN hL k hk member hScale) raw =
      DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed
        (fit D small hN hL k hk member hScale)
        (representative member.fullDim.connected
          (DegeneratePlacement.surviving_nonempty (D.bigSpec (small.scale k hk) hN hL)
            (degenerateLength D small) member) raw).1 :=
    (DegeneratePlacement.sourcePoint_survivor (D.bigSpec (small.scale k hk) hN hL)
      (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale)
      (representative member.fullDim.connected
        (DegeneratePlacement.surviving_nonempty (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member) raw)).symm
  rw [hEq]
  rcases DegeneratePlacement.survivor_cases (D.bigSpec (small.scale k hk) hN hL)
      (degenerateLength D small) member
      (representative member.fullDim.connected
        (DegeneratePlacement.surviving_nonempty (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member) raw) with ⟨branch, hb⟩ | ⟨address, ha⟩
  · rw [hb]
    exact Or.inl ⟨branch, (vertexMap_sourcePoint_branch D small hN hL k hk member hClosed
      hScale branch).symm⟩
  · rw [ha]
    exact Or.inr ⟨address, (vertexMap_sourcePoint_address D small hN hL k hk member hClosed
      hScale hCond address).symm⟩

/-- **The covering obligation, made checkable.**  `RealizationSurjective` — the
surjectivity of the member's realization onto the small subdivision, to which
`DegenerateFibreCover` reduces the covering half of its split of
`ForestContractionRank` — holds exactly when every small vertex is realized by
a branch label or by a row address at a realized offset.

This is a restatement, not a discharge: neither side is proved here. -/
theorem realizationSurjective_iff (hCond : D.Conditions small.core) :
    RealizationSurjective D small hN hL k hk member hClosed hScale ↔
      ∀ b : (small.scale k hk).Vertex,
        RealizedVertex D small hN hL k hk member hClosed b := by
  constructor
  · intro hSurj b
    obtain ⟨raw, hraw⟩ := hSurj b
    have hraw' : ExpansionData.vertexMap D (small.scale k hk) hN hL
        (DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member hClosed
          (fit D small hN hL k hk member hScale) raw) = b := hraw
    rw [← hraw']
    exact exists_realizedVertex_of_sourceVertex D small hN hL k hk member hClosed hScale
      hCond raw
  · intro hRealized b
    rcases hRealized b with ⟨branch, hb⟩ | ⟨address, ha⟩
    · exact ⟨branch.1, (vertexMap_sourcePoint_branch D small hN hL k hk member hClosed
        hScale branch).trans hb⟩
    · exact ⟨addressVertex member.fullDim address,
        (vertexMap_sourcePoint_address D small hN hL k hk member hClosed hScale hCond
          address).trans ha⟩

end DraismaVargas.Count.DegenerateRealizationImage
