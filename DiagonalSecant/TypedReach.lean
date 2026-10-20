module

public import DiagonalSecant.TypedTransport
public import GenusSixExistence.BrillNoetherRank.Tripod.RealisationProof

@[expose] public section

/-!
# The reach of the typed pencil, and rank one

The marked twin of `CorePencilCoverProducer.exists_pushDivisor_pos_fib` and of the loop-double
reach of `PencilTransportProducer.doubleRowInterior_of_loopDoubles`, assembled into rank one
by the public rank-determining set `RealisationProof.rankDetermining_of_fib_loopDoubles`
(Luo's criterion through the strong-separator lemma, `ChainSeparator`), which is stated for an
**arbitrary divisor** on `T = small.scale k` and asks reach only at the `D.fib` images and at a
vertex strictly inside the chain of every `double` slot **that displays a loop**.

That last restriction matters here: `MarkRefinement.exists_markStep` (the once-marked model,
`Model.lean`) can split a `double` at an interior point and produce a `double` whose chain is
not a loop, so `CorePencilCoverProducer.LoopDoubles` fails and the public
`markerFreePencilCoverSupply` cannot be used as a block; `rankDetermining_of_fib_loopDoubles`
asks nothing of a non-loop double, and the loop argument is made per slot here
(`loopDouble_interior`).

## Why every `D.fib` image is reached

Every big core vertex `a` is the label `κ.ident.vertex` of a marked branch vertex `b` (the label
is an equivalence); `b` is placed at `coreVertex a` and pushed to `coreVertex (D.fib a)`
(`TypedImage.realize_branch`), and it carries weight `blockCard ≥ 1` in the fibre over its own
target vertex. For the diagonal secant theorem, the mark is one of these `b`.
-/

namespace DiagonalSecant.TypedReach

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)
open DiagonalSecant.TypedRows DiagonalSecant.TypedPlacement DiagonalSecant.TypedImage
open DiagonalSecant.TypedTransport
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

variable {n p N Q m degree : ℕ} {mark : Fin m → Fin N} {types : Fin m → ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (κ : TypedFrame D.bigCore mark types degree)
  (hClosed : Closed (degenerateLength D small) κ)
  (hScale : scale (degenerateLength D small) κ = k)

/-! ## 1.  What the pencil reaches -/

/-- **Every `D.fib` image is reached** by the fibre over the target vertex of the marked branch
vertex labelled `a` (`CorePencilCoverProducer.exists_pushDivisor_pos_fib`). -/
theorem exists_pushed_pos_fib (a : Fin N) :
    ∃ root' : κ.target.V,
      0 < pushed D small hN hL k hk κ hClosed hScale root'
        ((small.scale k hk).coreVertex (D.fib a)) := by
  classical
  set b := κ.ident.vertex.symm a with hb
  refine ⟨b.1.1.1, ?_⟩
  rw [pushed_apply]
  have hb' : realize D small hN hL k hk κ hClosed hScale b.1 =
      (small.scale k hk).coreVertex (D.fib a) := by
    rw [realize_branch, hb, Equiv.apply_symm_apply]
  have hterm : (0 : ℤ) < if realize D small hN hL k hk κ hClosed hScale b.1 =
      (small.scale k hk).coreVertex (D.fib a) then fibre κ b.1.1.1 b.1 else 0 := by
    rw [ite_eq_left hb']
    unfold fibre
    rw [ite_eq_left rfl]
    exact_mod_cast SheetPartition.blockCard_pos _ _
  calc (0 : ℤ) < _ := hterm
    _ ≤ _ := Finset.single_le_sum
      (f := fun raw ↦ if realize D small hN hL k hk κ hClosed hScale raw =
        (small.scale k hk).coreVertex (D.fib a) then fibre κ b.1.1.1 raw else 0)
      (fun raw _ ↦ by split_ifs <;> [exact fibre_nonneg _ _ _; exact le_rfl])
      (Finset.mem_univ b.1)

/-! Local abbreviations for the proof of `loopDouble_interior` (unhygienic, so that they refer
to the section variables and to the slot `e` at the point of use). -/
set_option hygiene false in
local notation "RS" => CTTransport.rowStart (degenerateLength D small) κ hClosed
set_option hygiene false in
local notation "RL" => CTTransport.rowLen (degenerateLength D small) κ hClosed
set_option hygiene false in
local notation "BL" => (D.bigSpec (small.scale k hk) hN hL).length
set_option hygiene false in
local notation "LEN" => (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length
set_option hygiene false in
local notation "OV" => offsetVal (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ
  hClosed

/-- **A loop `double` is reached strictly inside its chain** by an interior address of the
frame's own row over that slot (`PencilTransportProducer.doubleRowInterior_of_loopDoubles`,
per slot, with the loop hypothesis for the one slot at hand). -/
theorem loopDouble_interior (hCond : D.Conditions small.core) {e : Fin Q} {j₁ j₂ : Fin p}
    (hkind : D.kind e = SlotKind.double j₁ j₂) (hloop : small.core.tail j₁ = small.core.head j₂) :
    ∃ (root' : κ.target.V) (t : ℕ), 0 < t ∧
      t < (small.scale k hk).length j₁ + (small.scale k hk).length j₂ ∧
      0 < pushed D small hN hL k hk κ hClosed hScale root'
        (kindVertex (small.scale k hk) (small.core.tail j₁) (SlotKind.double j₁ j₂) t) := by
  classical
  have hne : D.kind e ≠ SlotKind.contracted := by
    rw [hkind]
    exact fun h ↦ by cases h
  have hFull : RS e
      LEN = BL e :=
    CTTransport.rowStart_full_of_ne D small hN hL k hk κ hClosed hScale e hne
  have hLenB : BL e = (small.scale k hk).length j₁ + (small.scale k hk).length j₂ := by
    show kindLength (small.scale k hk) (D.kind e) = _
    rw [hkind]
    rfl
  have hLenPos := (D.bigSpec (small.scale k hk) hN hL).length_pos e
  obtain ⟨hTail, -, hHead⟩ :=
    (ExpansionData.compatible_of_conditions hCond e).2.2 j₁ j₂ hkind
  -- Step 1: some interior row vertex of `e` lies strictly inside the chain.
  have hEx : ∃ j, 0 < j ∧ j < LEN ∧
      0 < RS e j ∧ RS e j < BL e := by
    by_contra hNo
    push Not at hNo
    -- every interior prefix is `0` or the full length
    have hInt : ∀ j, 0 < j → j < LEN →
        RS e j = 0 ∨
          RS e j = BL e := by
      intro j hj0 hjl
      have hle : RS e j ≤ BL e :=
        (CTTransport.rowStart_le_full (degenerateLength D small) κ hClosed e j).trans hFull.le
      by_cases h0 : RS e j = 0
      · exact Or.inl h0
      · exact Or.inr (le_antisymm hle (hNo j hj0 hjl (Nat.pos_of_ne_zero h0)))
    -- the first prefix to leave `0` jumps to the full length
    obtain ⟨i0, hL0, hOthers⟩ := RowAlgebra.exists_single_long
      (CTTransport.rowStart_succ (degenerateLength D small) κ hClosed e)
      (CTTransport.rowStart_zero (degenerateLength D small) κ hClosed e) hFull hLenPos hInt
    -- the separating potential, rising only along the target edge of the long occurrence
    set t := ((orderedRow κ.fullDim.pathEnds (rowOf κ e))[i0]).1.1 with ht
    let s : κ.target.edges → ℤ := fun t' ↦ if t' = t then 1 else 0
    let P : κ.target.V → ℤ := TreeMetricPotential.integrate
      (fun t' ↦ s t' *
        ((realization (degenerateLength D small) κ hClosed).targetLength t' : ℤ))
    have hRise : CTTransport.RiseCompatible (degenerateLength D small) κ hClosed s P := fun t' ↦
      TreeMetricPotential.integrate_rise κ.fullDim.targetConnected κ.fullDim.targetGenus _ t'
    have hFib : D.fib (D.bigCore.tail e) = D.fib (D.bigCore.head e) := by
      rw [hTail, hHead]
      exact hloop
    have hCP := SlotScriptKernel.eq_of_fib_eq D small _ hCond
      (CTTransport.corePotential_contracted D small hN hL k hk κ hClosed hScale s P hRise) hFib
    have hC := CTTransport.compat D small hN hL k hk κ hClosed hScale s P hRise
    have hEq : CTTransport.slotValue D small hN hL k hk κ hClosed s P e 0 =
        CTTransport.slotValue D small hN hL k hk κ hClosed s P e (BL e) :=
      (hC.tail e).trans (hCP.trans (hC.head e).symm)
    have hPsi : CTTransport.sourcePotential κ P
          (rowVertex κ.fullDim.pathEnds (rowOf κ e)
            LEN) =
        CTTransport.sourcePotential κ P (rowVertex κ.fullDim.pathEnds (rowOf κ e) 0) := by
      have hGe := @RowAlgebra.value_of_ge _ _ _ _ _
        (CTTransport.rowStart_succ (degenerateLength D small) κ hClosed e) _
        (CTTransport.sum_rowSlope_mul_rowLen (degenerateLength D small) κ hClosed s P hRise e)
      unfold CTTransport.slotValue RowAlgebra.orient at hEq
      cases hr : reverse κ e
      · simp only [hr, Bool.false_eq_true, ite_false, Nat.cast_zero] at hEq
        rw [RowAlgebra.value_of_nonpos _ _ _ _ le_rfl, hGe (by rw [hFull])] at hEq
        exact hEq.symm
      · simp only [hr, ite_true, Nat.cast_zero, sub_zero, sub_self] at hEq
        rw [hGe (by rw [hFull]), RowAlgebra.value_of_nonpos _ _ _ _ le_rfl] at hEq
        exact hEq
    have hTel :=
      CTTransport.sum_rowSlope_mul_rowLen (degenerateLength D small) κ hClosed s P hRise e
    rw [hPsi, sub_self, Finset.sum_eq_single i0 (fun i _ hi ↦ by rw [hOthers i hi]; simp)
      (by simp), hL0] at hTel
    have hSlope : CTTransport.rowSlope κ s e i0 ≠ 0 := by
      have hidx := GluingDatum.sourceEdgeIndex_pos κ.data
        (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i0]
      have hs : s t = 1 := ite_eq_left rfl
      unfold CTTransport.rowSlope CTTransport.edgeSlope
      rw [← ht, hs]
      split_ifs <;> omega
    rcases mul_eq_zero.mp hTel with h | h
    · exact hSlope h
    · exact absurd h (by exact_mod_cast hLenPos.ne')
  -- Step 2: that row vertex is reached by the fibre over its own target vertex.
  obtain ⟨j, hj0, hjl, h1, h2⟩ := hEx
  set address : InteriorAddress κ.fullDim := ⟨rowOf κ e, ⟨j - 1, by omega⟩⟩ with hAddress
  have hReal := realize_address D small hN hL k hk κ hClosed hScale hCond address
  have hRow : κ.ident.row address.1 = e := Equiv.apply_symm_apply _ _
  have hIdx : address.2.val + 1 = j := by
    show j - 1 + 1 = j
    omega
  rw [hRow, hIdx, hTail, hkind] at hReal
  refine ⟨(addressVertex κ.fullDim address).1.1, OV e j, ?_, ?_, ?_⟩
  · rw [CTTransport.offsetVal_eq]
    cases reverse κ e <;> simp <;> omega
  · rw [CTTransport.offsetVal_eq, ← hLenB]
    cases reverse κ e <;> simp <;> omega
  · rw [pushed_apply]
    have hterm : (0 : ℤ) < if realize D small hN hL k hk κ hClosed hScale
        (addressVertex κ.fullDim address) =
          kindVertex (small.scale k hk) (small.core.tail j₁) (SlotKind.double j₁ j₂)
            (OV e j) then
        fibre κ (addressVertex κ.fullDim address).1.1 (addressVertex κ.fullDim address)
      else 0 := by
      rw [ite_eq_left hReal]
      unfold fibre
      rw [ite_eq_left rfl]
      exact_mod_cast SheetPartition.blockCard_pos _ _
    calc (0 : ℤ) < _ := hterm
      _ ≤ _ := Finset.single_le_sum
        (f := fun raw ↦ if realize D small hN hL k hk κ hClosed hScale raw =
          kindVertex (small.scale k hk) (small.core.tail j₁) (SlotKind.double j₁ j₂)
            (OV e j) then
          fibre κ (addressVertex κ.fullDim address).1.1 raw else 0)
        (fun raw _ ↦ by split_ifs <;> [exact fibre_nonneg _ _ _; exact le_rfl])
        (Finset.mem_univ (addressVertex κ.fullDim address))

/-! ## 2.  Rank one -/

/-- **Rank at least one of the pushed fibre**, at every root (the typed
`ForestContractionRank`): the reached set — every `D.fib` image and a vertex strictly inside
every loop-double chain — is rank-determining (`rankDetermining_of_fib_loopDoubles`), and every
reached vertex is winnable from the fibre at `root` through the pencil transport
(`pencilTransport`, `winnable_sub_one_chip_of_linear_equiv`). -/
theorem rank_pushed_ge_one (hCond : D.Conditions small.core) (hConn : small.core.Connected)
    (root : κ.target.V) :
    rank (small.scale k hk).graph (pushed D small hN hL k hk κ hClosed hScale root) ≥ 1 := by
  classical
  let R : Set (small.scale k hk).Vertex :=
    {w | ∃ root' : κ.target.V, 0 < pushed D small hN hL k hk κ hClosed hScale root' w}
  refine GenusSixExistence.Tripod.RealisationProof.rankDetermining_of_fib_loopDoubles D
    (small.scale k hk) hCond ((small.scale k hk).graph_connected_of_coreConnected hConn) R
    (fun a ↦ exists_pushed_pos_fib D small hN hL k hk κ hClosed hScale a)
    (fun e j₁ j₂ hkind hloop ↦ ?_) _ (fun w hw ↦ ?_)
  · obtain ⟨root', t, ht0, htL, hpos⟩ :=
      loopDouble_interior D small hN hL k hk κ hClosed hScale hCond hkind hloop
    exact ⟨t, ht0, htL, root', hpos⟩
  · obtain ⟨root', hpos⟩ := hw
    exact GenusSixExistence.Tripod.RealisationProof.winnable_sub_one_chip_of_linear_equiv
      (pushed_effective D small hN hL k hk κ hClosed hScale root')
      (pencilTransport D small hN hL k hk κ hClosed hScale hCond root root') hpos

end DiagonalSecant.TypedReach
