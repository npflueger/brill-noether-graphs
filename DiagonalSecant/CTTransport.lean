module

public import DiagonalSecant.TypedImage
public import DraismaVargasCount.PencilTransportProducer

@[expose] public section

/-!
# The transport of a typed frame, twinned on marked rows

This is the argument of `PencilTransportProducer` §2–§7, with the `FibreMember` replaced by a
typed frame `κ` and the unmarked rows by the marked rows of `TypedRows`. Everything datum-level
or datum-free is reused: `TreeMetricPotential`, the refinement equation
`sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence` through `RowWalkKernel` (the
fibre difference `RowWalkKernel.sum_fibre_sub`, the row decomposition
`RowWalkKernel.sum_edges_eq_sum_rows` over the marked rows, the telescoping along a row and the
separating potential `RowWalkKernel.not_single_long`, for the walk `rowVertex_isWalk`), the row
arithmetic of `RowAlgebra` (the row potential `RowAlgebra.value`, its ends, and the window
computation `RowAlgebra.slot_sum`), `kindVertex_zero_eq`, `kindVertex_length_eq`, and the slot-value
scripts of `SlotScriptKernel` (compatibility from the row ends, descent through the contraction,
the pushed Laplacian slot by slot against `hit`, and `SlotScriptKernel.linear_equiv_of_slots`).

§1–§4 are generic in the core and the natural request `y` (as `TypedPlacement` is); §5–§7
work at the degenerate request on `D.bigSpec (small.scale k hk)`, as `TypedImage` does. The
development is stated for any **rise-compatible** target potential (`RiseCompatible`), so that
`TypedReach.loopDouble_interior` can use the same script with a separating potential.

No boundary term arises at a mark: a mark is a row end and a marked branch vertex, placed at the
big core vertex of its own label (`TypedImage.realize_branch`), exactly like a trivalent end.
-/

namespace DiagonalSecant.CTTransport

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.PendantRetraction
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength degenerateLength_contracted
  degenerateLength_of_ne kindLength_scale_of_ne_contracted)
open DiagonalSecant.TypedRows DiagonalSecant.TypedPlacement DiagonalSecant.TypedImage
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion
open Utilities.Certificate.ExplicitPotential (Core)

variable {N Q m degree : ℕ} {mark : Fin m → Fin N} {types : Fin m → ℕ}

/-! ## 1.  Rise-compatible target potentials -/

section Generic

variable {core : Core N Q} (y : Fin Q → ℕ) (κ : TypedFrame core mark types degree)
  (hClosed : Closed y κ)

/-- A target potential `P` with integral slopes `s`, rising along every target edge by its slope
times the **realized integral length** of that edge (`PencilTransportProducer.RiseCompatible`). -/
def RiseCompatible (s : κ.target.edges → ℤ) (P : κ.target.V → ℤ) : Prop :=
  ∀ edge : κ.target.edges,
    P (edge : κ.target.V × κ.target.V).2 - P (edge : κ.target.V × κ.target.V).1 =
      s edge * ((realization y κ hClosed).targetLength edge : ℤ)

/-- The integral tree slope with incidence `anchor − root` (`TreeMetricPotential.chipSlope`). -/
noncomputable def chipSlope (root anchor : κ.target.V) : κ.target.edges → ℤ :=
  TreeMetricPotential.chipSlope κ.data κ.fullDim.targetConnected κ.fullDim.targetGenus root
    anchor

/-- The tree potential integrating `chipSlope` against the realized target lengths. -/
noncomputable def chipPotential (root anchor : κ.target.V) : κ.target.V → ℤ :=
  TreeMetricPotential.chipPotential κ.data κ.fullDim.targetConnected κ.fullDim.targetGenus
    (realization y κ hClosed).targetLength root anchor

theorem chip_riseCompatible (root anchor : κ.target.V) :
    RiseCompatible y κ hClosed (chipSlope κ root anchor)
      (chipPotential y κ hClosed root anchor) :=
  fun t ↦ TreeMetricPotential.chipPotential_rise κ.data κ.fullDim.targetConnected
    κ.fullDim.targetGenus (realization y κ hClosed).targetLength root anchor t

/-! ## 1b.  The pulled-back potential -/

section Source

variable (s : κ.target.edges → ℤ) (P : κ.target.V → ℤ)

/-- The pulled-back potential on the source (`PencilTransportProducer.sourcePotential`). -/
def sourcePotential (x : κ.data.SourceVertex) : ℤ := P x.1.1

/-- The slope of the pulled-back potential along one source edge, per unit of its realized
length (`PencilTransportProducer.edgeSlope`). -/
def edgeSlope (edge : κ.data.SourceEdge) : ℤ :=
  s edge.1.1 * (κ.data.sourceEdgeIndex edge : ℤ)

end Source

/-! ## 1c.  One row: offsets and slopes -/

section RowDefs

/-- The integral offset, from the row's start, of the `i`-th row vertex. -/
noncomputable def rowStart (e : Fin Q) (i : ℕ) : ℕ :=
  integralPrefix κ.fullDim (realization y κ hClosed) (rowOf κ e) i

/-- The realized integral length of the `i`-th occurrence of the row. -/
noncomputable def rowLen (e : Fin Q)
    (i : Fin (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length) : ℕ :=
  (realization y κ hClosed).sourceLength
    (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]

end RowDefs

section RowSlopeDef

variable {core : Core N Q} (κ : TypedFrame core mark types degree) (s : κ.target.edges → ℤ)

/-- The slope of the pulled-back potential along the `i`-th occurrence, read in the row's own
direction. -/
noncomputable def rowSlope (e : Fin Q)
    (i : Fin (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length) : ℤ :=
  if (κ.data.sourceEnds (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]).1 =
      rowVertex κ.fullDim.pathEnds (rowOf κ e) i then
    edgeSlope κ s (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]
  else
    -edgeSlope κ s (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]

end RowSlopeDef

section RowData

theorem rowStart_succ (e : Fin Q)
    (i : Fin (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length) :
    rowStart y κ hClosed e (i.val + 1) =
      rowStart y κ hClosed e i + rowLen y κ hClosed e i :=
  integralPrefix_succ κ.fullDim _ _ i.isLt

theorem rowStart_zero (e : Fin Q) : rowStart y κ hClosed e 0 = 0 := by
  simp [rowStart, integralPrefix]

theorem rowStart_le_full (e : Fin Q) (j : ℕ) :
    rowStart y κ hClosed e j ≤
      rowStart y κ hClosed e (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length :=
  integralPrefix_le_full κ.fullDim _ _ j

theorem rowStart_add_rowLen_le (e : Fin Q)
    (i : Fin (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length) :
    rowStart y κ hClosed e i + rowLen y κ hClosed e i ≤
      rowStart y κ hClosed e (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length := by
  rw [← rowStart_succ]
  exact rowStart_le_full y κ hClosed e _

/-- The row vertices walk along the marked row. -/
theorem rowVertex_isWalk (e : Fin Q) :
    RowWalkKernel.IsWalk (orderedRow κ.fullDim.pathEnds (rowOf κ e))
      (rowVertex κ.fullDim.pathEnds (rowOf κ e)) := fun _ h ↦
  ⟨rowVertex_incident κ.fullDim.pathEnds _ h, rowVertex_succ κ.fullDim.pathEnds _ h⟩

end RowData

end Generic

/-! ## 5.  The realization on the small subdivision, row by row -/

section Realization

variable {n p : ℕ} (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (κ : TypedFrame D.bigCore mark types degree)
  (hClosed : Closed (degenerateLength D small) κ)
  (hScale : scale (degenerateLength D small) κ = k)

/-- **The pushed pencil difference, edge by edge**
(`PencilTransportProducer.pushDivisor_sub_eq`). -/
theorem pushed_sub_eq (root anchor : κ.target.V) (b : (small.scale k hk).Vertex) :
    pushed D small hN hL k hk κ hClosed hScale anchor b -
        pushed D small hN hL k hk κ hClosed hScale root b =
      ∑ edge : κ.data.SourceEdge, edgeSlope κ (chipSlope κ root anchor) edge *
        ((if realize D small hN hL k hk κ hClosed hScale (κ.data.sourceEnds edge).1 = b
            then 1 else 0) -
          (if realize D small hN hL k hk κ hClosed hScale (κ.data.sourceEnds edge).2 = b
            then 1 else 0)) := by
  classical
  rw [pushed_apply, pushed_apply, ← Finset.sum_sub_distrib]
  refine (Finset.sum_congr rfl fun raw _ ↦ ?_).trans (RowWalkKernel.sum_fibre_sub κ.data
    κ.fullDim.targetConnected κ.fullDim.targetGenus root anchor
    (realize D small hN hL k hk κ hClosed hScale) b)
  by_cases hb : realize D small hN hL k hk κ hClosed hScale raw = b
  · rw [ite_eq_left hb, ite_eq_left hb, ite_eq_left hb]
    rfl
  · rw [ite_eq_right hb, ite_eq_right hb, ite_eq_right hb]
    ring

/-- A dangling edge is collapsed by the realization. -/
theorem realize_dangling {edge : κ.data.SourceEdge} (hD : IsDangling κ.data edge) :
    realize D small hN hL k hk κ hClosed hScale (κ.data.sourceEnds edge).1 =
      realize D small hN hL k hk κ hClosed hScale (κ.data.sourceEnds edge).2 := by
  have hRetract : retractVertex (κ.data.sourceEnds edge).1 =
      retractVertex (κ.data.sourceEnds edge).2 :=
    Quotient.sound (Relation.ReflTransGen.single ⟨edge, hD, Or.inl rfl⟩)
  exact congrArg (ExpansionData.vertexMap D (small.scale k hk) hN hL)
    (sourcePoint_of_retract (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ
      hClosed (fit D small hN hL k hk κ hScale) hRetract)

/-- A marked branch vertex labelled by an end of `e`, placed at that end, is realized as
`kindVertex` there (`PencilTransportProducer.realization_branch_end`). -/
theorem realize_branch_end (hCond : D.Conditions small.core) (e : Fin Q)
    (branch : MarkedBranchVertex κ.data (markSet κ.markSource)) (rev : Bool)
    (hLabel : κ.ident.vertex branch = if rev then D.bigCore.head e else D.bigCore.tail e) :
    realize D small hN hL k hk κ hClosed hScale branch.1 =
      kindVertex (small.scale k hk) (D.fib (D.bigCore.tail e)) (D.kind e)
        (if rev then (D.bigSpec (small.scale k hk) hN hL).length e else 0) := by
  refine (realize_branch D small hN hL k hk κ hClosed hScale branch).trans ?_
  rw [hLabel]
  cases rev
  · simp only [Bool.false_eq_true, ite_false]
    exact (PencilTransportProducer.kindVertex_zero_eq D small hN hL k hk hCond e).symm
  · simp only [ite_true]
    exact (PencilTransportProducer.kindVertex_length_eq D small hN hL k hk hCond e).symm

include hScale in
/-- The full prefix of a non-contracted slot is its big length. -/
theorem rowStart_full_of_ne (e : Fin Q) (hne : D.kind e ≠ SlotKind.contracted) :
    rowStart (degenerateLength D small) κ hClosed e
        (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length =
      (D.bigSpec (small.scale k hk) hN hL).length e := by
  unfold rowStart
  rw [integralPrefix_full (degenerateLength D small) κ hClosed e, hScale,
    degenerateLength_of_ne D small hne]
  show k * kindLength small (D.kind e) = kindLength (small.scale k hk) (D.kind e)
  rw [kindLength_scale_of_ne_contracted small k hk hne]

/-- The full prefix of a contracted slot is `0`. -/
theorem rowStart_full_of_contracted (e : Fin Q) (hc : D.kind e = SlotKind.contracted) :
    rowStart (degenerateLength D small) κ hClosed e
        (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length = 0 := by
  unfold rowStart
  rw [integralPrefix_full (degenerateLength D small) κ hClosed e,
    degenerateLength_contracted D small hc, Nat.mul_zero]

/-- `offsetVal`, in terms of `rowStart`. -/
theorem offsetVal_eq (e : Fin Q) (j : ℕ) :
    offsetVal (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ hClosed e j =
      if reverse κ e then
        (D.bigSpec (small.scale k hk) hN hL).length e -
          rowStart (degenerateLength D small) κ hClosed e j
      else rowStart (degenerateLength D small) κ hClosed e j := rfl

/-- **Every row vertex is realized at its own oriented offset**
(`PencilTransportProducer.realization_rowVertex`). At the two ends this is the branch placement
(a mark included); on a contracted slot `kindVertex` is constant and the two ends lie in one
fibre. -/
theorem realize_rowVertex (hCond : D.Conditions small.core) (e : Fin Q) (j : ℕ)
    (hj : j ≤ (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length) :
    realize D small hN hL k hk κ hClosed hScale (rowVertex κ.fullDim.pathEnds (rowOf κ e) j) =
      kindVertex (small.scale k hk) (D.fib (D.bigCore.tail e)) (D.kind e)
        (offsetVal (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ hClosed
          e j) := by
  have hEnds := reverse_endpoints κ hL e
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- the start branch
    have h := realize_branch_end D small hN hL k hk κ hClosed hScale hCond e
      (startBranch κ.fullDim (rowOf κ e)) (reverse κ e) hEnds.1
    refine h.trans ?_
    rw [offsetVal_eq, rowStart_zero]
    cases reverse κ e <;> rfl
  by_cases hjl : j = (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length
  · -- the finish branch
    subst hjl
    have h := realize_branch_end D small hN hL k hk κ hClosed hScale hCond e
      (finishBranch κ.fullDim (rowOf κ e)) (!reverse κ e)
      (by rw [hEnds.2]; cases reverse κ e <;> rfl)
    by_cases hc : D.kind e = SlotKind.contracted
    · have hFib := (ExpansionData.compatible_of_conditions hCond e).1 hc
      have hv := realize_branch D small hN hL k hk κ hClosed hScale
        (finishBranch κ.fullDim (rowOf κ e))
      refine hv.trans ?_
      rw [hc, hEnds.2]
      show _ = (small.scale k hk).coreVertex (D.fib (D.bigCore.tail e))
      split_ifs
      · rfl
      · rw [hFib]
    · refine h.trans ?_
      have hP := rowStart_full_of_ne D small hN hL k hk κ hClosed hScale e hc
      rw [offsetVal_eq, hP]
      cases reverse κ e <;> simp
  · -- an interior address
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h := realize_address D small hN hL k hk κ hClosed hScale hCond
      ⟨rowOf κ e, ⟨i, by omega⟩⟩
    simp only [rowOf, Equiv.apply_symm_apply] at h
    exact h

end Realization

/-! ## 6.  The big-side script, its descent -/

section Script

variable {n p : ℕ} (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (κ : TypedFrame D.bigCore mark types degree)
  (hClosed : Closed (degenerateLength D small) κ)
  (hScale : scale (degenerateLength D small) κ = k)
  (s : κ.target.edges → ℤ) (P : κ.target.V → ℤ)

/-- The script's value at offset `o` of big slot `e`: the row potential (`RowAlgebra.value`) at
the oriented position (`RowAlgebra.orient`). -/
noncomputable def slotValue (e : Fin Q) (o : ℕ) : ℤ :=
  RowAlgebra.value (sourcePotential κ P (rowVertex κ.fullDim.pathEnds (rowOf κ e) 0))
    (rowSlope κ s e) (rowStart (degenerateLength D small) κ hClosed e)
    (rowLen (degenerateLength D small) κ hClosed e)
    (RowAlgebra.orient (reverse κ e) ((D.bigSpec (small.scale k hk) hN hL).length e) o)

/-- The script's value at a big core vertex: the pulled-back potential at the marked branch
vertex carrying that label (a mark, or a trivalent vertex). -/
noncomputable def corePotential (v : Fin N) : ℤ :=
  sourcePotential κ P (κ.ident.vertex.symm v).1

theorem corePotential_ident (branch : MarkedBranchVertex κ.data (markSet κ.markSource)) :
    corePotential D κ P (κ.ident.vertex branch) = sourcePotential κ P branch.1 := by
  simp [corePotential]

include hScale in
theorem rowStart_full_le_length (e : Fin Q) :
    rowStart (degenerateLength D small) κ hClosed e
        (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length ≤
      (D.bigSpec (small.scale k hk) hN hL).length e := by
  by_cases hc : D.kind e = SlotKind.contracted
  · rw [rowStart_full_of_contracted D small κ hClosed e hc]
    exact Nat.zero_le _
  · exact (rowStart_full_of_ne D small hN hL k hk κ hClosed hScale e hc).le

include hScale in
/-- The script is compatible with the core potential at both ends of every slot. -/
theorem compat (hRise : RiseCompatible (degenerateLength D small) κ hClosed s P) :
    (D.bigSpec (small.scale k hk) hN hL).SlotValueCompatible (corePotential D κ P)
      (slotValue D small hN hL k hk κ hClosed s P) := by
  have hFull := rowStart_full_le_length D small hN hL k hk κ hClosed hScale
  refine SlotScriptKernel.compat_of_ends D small hN hL k hk _
    (fun e ↦ RowAlgebra.value (sourcePotential κ P (rowVertex κ.fullDim.pathEnds (rowOf κ e) 0))
      (rowSlope κ s e) (rowStart (degenerateLength D small) κ hClosed e)
      (rowLen (degenerateLength D small) κ hClosed e)) (reverse κ)
    (fun e pos hpos ↦ ?_) (fun e pos hpos ↦ ?_)
  · rw [RowAlgebra.value_of_nonpos _ _ _ _ hpos, ← (reverse_endpoints κ hL e).1,
      corePotential_ident]
    rfl
  · rw [RowAlgebra.value_of_ge (sourcePotential κ P (rowVertex κ.fullDim.pathEnds (rowOf κ e) 0))
      (rowSlope κ s e) (rowStart_succ (degenerateLength D small) κ hClosed e)
      (RowWalkKernel.sum_slope_mul_len _ (rowVertex_isWalk κ e) hRise)
      (by have := hFull e; omega), ← (reverse_endpoints κ hL e).2, corePotential_ident]
    rfl

include hN hL hk hScale in
/-- The two ends of a contracted slot carry the same core potential. -/
theorem corePotential_contracted (hRise : RiseCompatible (degenerateLength D small) κ hClosed s P)
    (e : Fin Q) (hc : D.kind e = SlotKind.contracted) :
    corePotential D κ P (D.bigCore.tail e) = corePotential D κ P (D.bigCore.head e) := by
  have hC := compat D small hN hL k hk κ hClosed hScale s P hRise
  have h1 : corePotential D κ P (D.bigCore.tail e) =
      slotValue D small hN hL k hk κ hClosed s P e 0 := (hC.tail e).symm
  have h2 : corePotential D κ P (D.bigCore.head e) =
      slotValue D small hN hL k hk κ hClosed s P e
        ((D.bigSpec (small.scale k hk) hN hL).length e) := (hC.head e).symm
  have h0 := rowStart_full_of_contracted D small κ hClosed e hc
  have hLen : ∀ i, rowLen (degenerateLength D small) κ hClosed e i = 0 := fun i ↦ by
    have h := rowStart_add_rowLen_le (degenerateLength D small) κ hClosed e i
    rw [h0] at h
    omega
  rw [h1, h2]
  unfold slotValue
  rw [RowAlgebra.value_of_len_zero _ _ _ _ hLen, RowAlgebra.value_of_len_zero _ _ _ _ hLen]

end Script

/-! ## 7.  Both sides, slot by slot -/

section Compare

variable {n p : ℕ} (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (κ : TypedFrame D.bigCore mark types degree)
  (hClosed : Closed (degenerateLength D small) κ)
  (hScale : scale (degenerateLength D small) κ = k)
  (root anchor : κ.target.V)

/-! Local abbreviations for the slot-by-slot computation (unhygienic, so that they refer to the
section variables at the point of use). -/
set_option hygiene false in
local notation "RSl" => rowSlope κ (chipSlope κ root anchor)
set_option hygiene false in
local notation "OV" => offsetVal (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) κ
  hClosed
set_option hygiene false in
local notation "HIT" => PencilTransportProducer.hit D small k hk

/-- **The small side of the identity**: the pushed pencil difference, as a sum over the frame's
marked rows (`PencilTransportProducer.pushDivisor_sub_eq_rows`). -/
theorem pushed_sub_eq_rows (hCond : D.Conditions small.core) (b : (small.scale k hk).Vertex) :
    pushed D small hN hL k hk κ hClosed hScale anchor b -
        pushed D small hN hL k hk κ hClosed hScale root b =
      ∑ e : Fin Q, ∑ i : Fin (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length,
        RSl e i *
          (HIT e b
              (OV e i) -
            HIT e b
              (OV e (i.val + 1))) := by
  classical
  rw [pushed_sub_eq]
  rw [RowWalkKernel.sum_edges_eq_sum_rows κ.data
      (fun e ↦ orderedRow κ.fullDim.pathEnds (rowOf κ e))
      (fun _ ↦ orderedRow_nodup κ.fullDim.pathEnds _)
      (fun edge hD ↦ ⟨κ.ident.row (markedRow (markSet κ.markSource) ⟨edge, hD⟩),
        (mem_orderedRow_iff κ.fullDim.pathEnds _ edge).mpr
          ⟨hD, by rw [rowOf, Equiv.symm_apply_apply]⟩,
        fun e he ↦ by
          obtain ⟨_, hP⟩ := (mem_orderedRow_iff κ.fullDim.pathEnds _ edge).mp he
          rw [hP, rowOf, Equiv.apply_symm_apply]⟩)
      (fun edge ↦ edgeSlope κ (chipSlope κ root anchor) edge *
      ((if realize D small hN hL k hk κ hClosed hScale (κ.data.sourceEnds edge).1 = b
          then 1 else 0) -
        (if realize D small hN hL k hk κ hClosed hScale (κ.data.sourceEnds edge).2 = b
          then 1 else 0)))
    (fun edge hD ↦ by
      rw [realize_dangling D small hN hL k hk κ hClosed hScale hD]
      ring)]
  refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  refine (RowWalkKernel.slope_mul_sub (rowVertex_isWalk κ e) (chipSlope κ root anchor) i
    (fun v ↦ if realize D small hN hL k hk κ hClosed hScale v = b then 1 else 0)).symm.trans ?_
  unfold PencilTransportProducer.hit
  rw [realize_rowVertex D small hN hL k hk κ hClosed hScale hCond e i (le_of_lt i.isLt),
    realize_rowVertex D small hN hL k hk κ hClosed hScale hCond e (i.val + 1) i.isLt]
  rfl

include hScale in
/-- **(T), typed.** Any two pushed fibres of a closed typed frame are linearly equivalent on the
small subdivision: their difference is the Laplacian of the descended script
(`PencilTransportProducer.linear_equiv_pushDivisor`). -/
theorem linear_equiv_pushed (hCond : D.Conditions small.core) :
    linear_equiv (small.scale k hk).graph
      (pushed D small hN hL k hk κ hClosed hScale root)
      (pushed D small hN hL k hk κ hClosed hScale anchor) :=
  have hRise := chip_riseCompatible (degenerateLength D small) κ hClosed root anchor
  SlotScriptKernel.linear_equiv_of_slots D small hN hL k hk _ _ hCond
    (fun _ _ ↦ SlotScriptKernel.eq_of_fib_eq D small _ hCond
      (corePotential_contracted D small hN hL k hk κ hClosed hScale _ _ hRise))
    (compat D small hN hL k hk κ hClosed hScale _ _ hRise) _ _ fun b ↦ by
      rw [pushed_sub_eq_rows D small hN hL k hk κ hClosed hScale root anchor hCond b]
      exact Finset.sum_congr rfl fun e _ ↦ (RowAlgebra.slot_sum _ _
        (rowStart_succ (degenerateLength D small) κ hClosed e) (reverse κ e) _
        (fun i ↦ (rowStart_add_rowLen_le (degenerateLength D small) κ hClosed e i).trans
          (rowStart_full_le_length D small hN hL k hk κ hClosed hScale e)) (HIT e b)).symm

end Compare

end DiagonalSecant.CTTransport
