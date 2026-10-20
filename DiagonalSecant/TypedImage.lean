module

public import DiagonalSecant.TypedPlacement
public import DraismaVargasCount.DegenerateBigDivisor
public import DraismaVargasCount.DegenerateRealizationImage

@[expose] public section

/-!
# The typed big divisor at the degenerate request, and its image

The marked twin of
`DegenerateBigDivisor` §1–§3 and of `DegenerateRealizationImage`: the target is
`D.bigSpec (small.scale k hk) hN hL`, the request the **degenerate** one (`degenerateLength`,
public and reused), the typed frame `κ` over `D.bigCore` closed there with scale `k`.

What is new against the public module is one family: a mark `u_j` is placed at the big core
vertex `mark j` (`TypedPlacement.sourcePoint_mark`), so its realization on the small side is
`coreVertex (D.fib (mark j))` (`realize_mark`), and the pushed fibre over the **image of the
mark** carries at least the mark's local degree there (`markIndex_le_pushed`). This is where the
chips `(g − 3) ū` of the diagonal secant theorem come from: for the model of `Defs.lean`,
`D.fib (Fin.last N) = smallMark` (`OnceMarkedModel.fib_mark`) and
`markIndex ≥ a + 1 = g − 3` by (D4′) (`TypedFrame.typed`).

`pushDivisor`, `effective_pushDivisor` and `deg_pushDivisor` (`ExpansionSeriesMoment`) are
datum-free and reused.
-/

namespace DiagonalSecant.TypedImage

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.PendantRetraction DraismaVargas.Count.CanonicalSurvivor
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength degenerateLength_contracted
  degenerateLength_of_ne kindLength_scale_of_ne_contracted)
open DiagonalSecant.TypedRows DiagonalSecant.TypedPlacement
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

variable {n p N Q m degree : ℕ} {mark : Fin m → Fin N} {types : Fin m → ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)

/-! ## 1.  The two receipts `TypedPlacement` asks for -/

section Receipts

variable (κ : TypedFrame D.bigCore mark types degree)
  (hScale : scale (degenerateLength D small) κ = k)

include hScale in
/-- **The fit**: the frame fills a retained slot exactly and falls one unit short on a
contracted one (`DegenerateBigDivisor.fit`). -/
theorem fit (e : Fin Q) :
    scale (degenerateLength D small) κ * degenerateLength D small e ≤
      (D.bigSpec (small.scale k hk) hN hL).length e := by
  have hlen : (D.bigSpec (small.scale k hk) hN hL).length e =
      kindLength (small.scale k hk) (D.kind e) := rfl
  rw [hScale, hlen]
  by_cases h : D.kind e = SlotKind.contracted
  · rw [degenerateLength_contracted D small h, Nat.mul_zero]
    exact Nat.zero_le _
  · rw [degenerateLength_of_ne D small h, kindLength_scale_of_ne_contracted small k hk h]

include hScale in
/-- **The exactness, where it is used**: a big slot with an interior vertex is filled exactly
(`DegenerateBigDivisor.exact`). -/
theorem exact (e : Fin Q) (hTwo : 1 < (D.bigSpec (small.scale k hk) hN hL).length e) :
    scale (degenerateLength D small) κ * degenerateLength D small e =
      (D.bigSpec (small.scale k hk) hN hL).length e := by
  have hlen : (D.bigSpec (small.scale k hk) hN hL).length e =
      kindLength (small.scale k hk) (D.kind e) := rfl
  rw [hlen] at hTwo ⊢
  rw [hScale]
  by_cases h : D.kind e = SlotKind.contracted
  · rw [h] at hTwo
    exact absurd hTwo (by simp [kindLength])
  · rw [degenerateLength_of_ne D small h, kindLength_scale_of_ne_contracted small k hk h]

end Receipts

/-! ## 2.  The big divisor and its pushforward -/

section Divisor

variable (κ : TypedFrame D.bigCore mark types degree)
  (hClosed : Closed (degenerateLength D small) κ)
  (hScale : scale (degenerateLength D small) κ = k)

/-- **The big-side divisor at the degenerate request**: the placement of `κ` on
`D.bigSpec (small.scale k)`, pushed from the pullback fibre over `root`. -/
noncomputable def bigDivisor (root : κ.target.V) :
    CFDiv (D.bigSpec (small.scale k hk) hN hL).graph :=
  divisor (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ hClosed
    (fit D small hN hL k hk κ hScale) root

theorem bigDivisor_effective (root : κ.target.V) :
    effective (bigDivisor D small hN hL k hk κ hClosed hScale root) :=
  divisor_effective _ _ _ _ _ _

theorem bigDivisor_degree (root : κ.target.V) :
    deg (bigDivisor D small hN hL k hk κ hClosed hScale root) = (degree : ℤ) :=
  divisor_degree _ _ _ _ _ _

/-- **The realization**: the placement followed by the contraction, one map from the source
graph onto the small subdivision. -/
noncomputable def realize : κ.data.SourceVertex → (small.scale k hk).Vertex :=
  ExpansionData.vertexMap D (small.scale k hk) hN hL ∘
    sourcePoint (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ hClosed
      (fit D small hN hL k hk κ hScale)

/-- **The pushed divisor**: the big divisor pushed along the contraction, a divisor on
`small.scale k`. This is the divisor `W` of the realisation. -/
noncomputable def pushed (root : κ.target.V) : CFDiv (small.scale k hk).graph :=
  ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
    (bigDivisor D small hN hL k hk κ hClosed hScale root)

/-- The pushed divisor is the pushforward of the fibre along the realization
(`DegenerateBigDivisor.pushDivisor_bigDivisor`). -/
theorem pushed_eq_push (root : κ.target.V) :
    pushed D small hN hL k hk κ hClosed hScale root =
      PendantDivisorTransport.push (realize D small hN hL k hk κ hClosed hScale)
        (fibre κ root) :=
  (PendantDivisorTransport.push_comp (G := κ.data.sourceGraph)
      (H := (D.bigSpec (small.scale k hk) hN hL).graph) (K := (small.scale k hk).graph)
      (sourcePoint (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ hClosed
        (fit D small hN hL k hk κ hScale))
      (ExpansionData.vertexMap D (small.scale k hk) hN hL)
      (fibre κ root)).symm

theorem pushed_apply (root : κ.target.V) (b : (small.scale k hk).Vertex) :
    pushed D small hN hL k hk κ hClosed hScale root b =
      ∑ raw : κ.data.SourceVertex,
        if realize D small hN hL k hk κ hClosed hScale raw = b then
          fibre κ root raw else 0 := by
  rw [pushed_eq_push]
  rfl

theorem pushed_effective (root : κ.target.V) :
    effective (pushed D small hN hL k hk κ hClosed hScale root) :=
  ExpansionSeriesMoment.effective_pushDivisor _ (bigDivisor_effective D small hN hL k hk κ hClosed
    hScale root)

theorem deg_pushed (root : κ.target.V) :
    deg (pushed D small hN hL k hk κ hClosed hScale root) = (degree : ℤ) := by
  rw [pushed, ExpansionSeriesMoment.deg_pushDivisor, bigDivisor_degree]

end Divisor

/-! ## 3.  The image of the realization -/

section Image

variable (κ : TypedFrame D.bigCore mark types degree)
  (hClosed : Closed (degenerateLength D small) κ)
  (hScale : scale (degenerateLength D small) κ = k)

/-- **A marked branch vertex realizes the small core vertex `D.fib` of its label**
(`DegenerateRealizationImage.vertexMap_sourcePoint_branch`). -/
theorem realize_branch (branch : MarkedBranchVertex κ.data (markSet κ.markSource)) :
    realize D small hN hL k hk κ hClosed hScale branch.1 =
      (small.scale k hk).coreVertex (D.fib (κ.ident.vertex branch)) := by
  have hStep := sourcePoint_branch (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small)
    κ hClosed (fit D small hN hL k hk κ hScale) branch
  show ExpansionData.vertexMap D (small.scale k hk) hN hL _ = _
  rw [hStep]
  rfl

/-- **A mark realizes `D.fib (mark j)`.** -/
theorem realize_mark (j : Fin m) :
    realize D small hN hL k hk κ hClosed hScale (κ.markSource j) =
      (small.scale k hk).coreVertex (D.fib (mark j)) := by
  have hStep := sourcePoint_mark (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small)
    κ hClosed (fit D small hN hL k hk κ hScale) j
  show ExpansionData.vertexMap D (small.scale k hk) hN hL _ = _
  rw [hStep]
  rfl

/-- **An interior row address realizes `kindVertex` at its own oriented offset**
(`DegenerateRealizationImage.vertexMap_sourcePoint_address`). On a contracted slot `kindVertex`
discards the offset: that is the forest contraction. -/
theorem realize_address (hCond : D.Conditions small.core) (address : InteriorAddress κ.fullDim) :
    realize D small hN hL k hk κ hClosed hScale (addressVertex κ.fullDim address) =
      kindVertex (small.scale k hk) (D.fib (D.bigCore.tail (κ.ident.row address.1)))
        (D.kind (κ.ident.row address.1))
        (offsetVal (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ hClosed
          (κ.ident.row address.1) (address.2.val + 1)) := by
  have hSurv : 0 < nonDanglingValency κ.data (addressVertex κ.fullDim address) := by
    have := addressVertex_valency κ.fullDim address
    omega
  have hStep : sourcePoint (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ
      hClosed (fit D small hN hL k hk κ hScale) (addressVertex κ.fullDim address) =
      addressPoint (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ hClosed
        (fit D small hN hL k hk κ hScale) address :=
    (sourcePoint_survivor (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ
        hClosed (fit D small hN hL k hk κ hScale) ⟨addressVertex κ.fullDim address, hSurv⟩).trans
      (survivingPoint_address (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ
        hClosed (fit D small hN hL k hk κ hScale) address)
  show ExpansionData.vertexMap D (small.scale k hk) hN hL _ = _
  rw [hStep]
  exact ExpansionData.vertexMap_pathVertex (D := D) (small := small.scale k hk) (hN := hN)
    (hL := hL) hCond (κ.ident.row address.1)
    (position (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ hClosed
      (fit D small hN hL k hk κ hScale) (κ.ident.row address.1) (address.2.val + 1))

/-- **The chips at the image of a mark.** The pushed fibre over the mark's own target vertex has
at least the mark's local degree at `coreVertex (D.fib (mark j))`: the mark contributes
`markIndex` there (`fibre_mark`, `realize_mark`) and every other term is nonnegative. -/
theorem markIndex_le_pushed (j : Fin m) :
    (markIndex κ.data (κ.markSource j) : ℤ) ≤
      pushed D small hN hL k hk κ hClosed hScale (κ.markSource j).1.1
        ((small.scale k hk).coreVertex (D.fib (mark j))) := by
  classical
  rw [pushed_apply]
  have hterm : (markIndex κ.data (κ.markSource j) : ℤ) =
      if realize D small hN hL k hk κ hClosed hScale (κ.markSource j) =
          (small.scale k hk).coreVertex (D.fib (mark j)) then
        fibre κ (κ.markSource j).1.1 (κ.markSource j)
      else 0 := by
    rw [ite_eq_left (realize_mark D small hN hL k hk κ hClosed hScale j), fibre_mark]
  rw [hterm]
  exact Finset.single_le_sum (f := fun raw ↦ if realize D small hN hL k hk κ hClosed hScale raw =
      (small.scale k hk).coreVertex (D.fib (mark j)) then
        fibre κ (κ.markSource j).1.1 raw else 0)
    (fun raw _ ↦ by split_ifs <;> [exact fibre_nonneg _ _ _; exact le_rfl])
    (Finset.mem_univ (κ.markSource j))

end Image

end DiagonalSecant.TypedImage
