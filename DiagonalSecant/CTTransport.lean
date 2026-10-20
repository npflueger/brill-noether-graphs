module

public import DiagonalSecant.TypedImage
public import DraismaVargasCount.PencilTransportProducer

@[expose] public section

/-!
# The transport of a typed frame, twinned on marked rows

This is `PencilTransportProducer` §2–§7, statement for statement, with the `FibreMember`
replaced by a typed frame `κ` and the unmarked rows by the marked rows of `TypedRows`. Everything
datum-level or datum-free is reused: `TreeMetricPotential`, the refinement equation
`sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence`, the row arithmetic of
`RowAlgebra` (the row potential `RowAlgebra.value`, its ends, and the window computation
`RowAlgebra.slot_sum`), `kindVertex_zero_eq`, `kindVertex_length_eq`, `hit`, and the scripts of
`Utilities.Subdivision.CoreExpansion` (`slotValueScript`, `prin_eq_sum_slopes`,
`pushDiv_prin_pullScript`).

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

/-! ## 1b.  The source side: the fibre difference is a pulled-back incidence -/

section Source

variable (s : κ.target.edges → ℤ) (P : κ.target.V → ℤ)

/-- The pulled-back potential on the source (`PencilTransportProducer.sourcePotential`). -/
def sourcePotential (x : κ.data.SourceVertex) : ℤ := P x.1.1

/-- The slope of the pulled-back potential along one source edge, per unit of its realized
length (`PencilTransportProducer.edgeSlope`). -/
def edgeSlope (edge : κ.data.SourceEdge) : ℤ :=
  s edge.1.1 * (κ.data.sourceEdgeIndex edge : ℤ)

/-- Along a source edge the pulled-back potential rises by the edge slope times the realized
source length: the dilation equation (`PencilTransportProducer.sourcePotential_rise`). -/
theorem sourcePotential_rise (hRise : RiseCompatible y κ hClosed s P)
    (edge : κ.data.SourceEdge) :
    sourcePotential κ P (κ.data.sourceEnds edge).2 -
        sourcePotential κ P (κ.data.sourceEnds edge).1 =
      edgeSlope κ s edge *
        ((realization y κ hClosed).sourceLength edge : ℤ) := by
  have h := hRise edge.1.1
  have hDil := (realization y κ hClosed).dilation_length edge
  have hDilZ : ((κ.data.sourceEdgeIndex edge : ℕ) : ℤ) *
      ((realization y κ hClosed).sourceLength edge : ℤ) =
      ((realization y κ hClosed).targetLength edge.1.1 : ℤ) := by
    exact_mod_cast hDil
  unfold sourcePotential edgeSlope
  change P (edge.1.1 : κ.target.V × κ.target.V).2 -
    P (edge.1.1 : κ.target.V × κ.target.V).1 = _
  rw [h, ← hDilZ]
  ring

/-- **The fibre difference is the pulled-back incidence** (`PencilTransportProducer.fibre_sub_eq`):
the sheet-partition refinement equation against the tree slope with incidence `anchor − root`. -/
theorem fibre_sub_eq (root anchor : κ.target.V) (raw : κ.data.SourceVertex) :
    fibre κ anchor raw - fibre κ root raw =
      ∑ edge : κ.data.SourceEdge,
        ((if (κ.data.sourceEnds edge).1 = raw then
            edgeSlope κ (chipSlope κ root anchor) edge else 0) -
          (if (κ.data.sourceEnds edge).2 = raw then
            edgeSlope κ (chipSlope κ root anchor) edge else 0)) := by
  have h := κ.data.sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence
    (chipSlope κ root anchor) raw
  have hInc := TreeMetricPotential.chipSlope_incidence κ.data
    κ.fullDim.targetConnected κ.fullDim.targetGenus root anchor raw.1.1
  unfold sourceEdgeIncidence at h
  change _ = ((κ.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) *
    targetEdgeIncidence (chipSlope κ root anchor) raw.1.1 at h
  unfold chipSlope at h
  rw [hInc] at h
  have hL : ∑ edge : κ.data.SourceEdge,
      ((if (κ.data.sourceEnds edge).1 = raw then
          edgeSlope κ (chipSlope κ root anchor) edge else 0) -
        (if (κ.data.sourceEnds edge).2 = raw then
          edgeSlope κ (chipSlope κ root anchor) edge else 0)) =
      ∑ edge : κ.data.SourceEdge,
        ((if (κ.data.sourceEnds edge).1 = raw then
            (κ.data.sourceEdgeIndex edge : ℤ) *
              TreeMetricPotential.chipSlope κ.data κ.fullDim.targetConnected
                κ.fullDim.targetGenus root anchor edge.1.1 else 0) +
          (if (κ.data.sourceEnds edge).2 = raw then
            (κ.data.sourceEdgeIndex edge : ℤ) *
              -TreeMetricPotential.chipSlope κ.data κ.fullDim.targetConnected
                κ.fullDim.targetGenus root anchor edge.1.1 else 0)) := by
    refine Finset.sum_congr rfl fun edge _ ↦ ?_
    unfold edgeSlope chipSlope
    split_ifs <;> ring
  rw [hL, h]
  unfold fibre
  split_ifs <;> ring

/-- **The pushed fibre difference, edge by edge**, along any map out of the source
(`PencilTransportProducer.sum_fibre_sub`). -/
theorem sum_fibre_sub (root anchor : κ.target.V) {X : Type*} [DecidableEq X]
    (ρ : κ.data.SourceVertex → X) (b : X) :
    (∑ raw : κ.data.SourceVertex,
      if ρ raw = b then fibre κ anchor raw - fibre κ root raw else 0) =
      ∑ edge : κ.data.SourceEdge, edgeSlope κ (chipSlope κ root anchor) edge *
        ((if ρ (κ.data.sourceEnds edge).1 = b then 1 else 0) -
          (if ρ (κ.data.sourceEnds edge).2 = b then 1 else 0)) := by
  classical
  have hStep : ∀ raw : κ.data.SourceVertex,
      (if ρ raw = b then fibre κ anchor raw - fibre κ root raw else 0) =
        ∑ edge : κ.data.SourceEdge,
          (if ρ raw = b then
            ((if (κ.data.sourceEnds edge).1 = raw then
                edgeSlope κ (chipSlope κ root anchor) edge else 0) -
              (if (κ.data.sourceEnds edge).2 = raw then
                edgeSlope κ (chipSlope κ root anchor) edge else 0)) else 0) := by
    intro raw
    by_cases hb : ρ raw = b
    · simp only [ite_eq_left hb]
      exact fibre_sub_eq κ root anchor raw
    · simp only [ite_eq_right hb, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun raw _ ↦ hStep raw, Finset.sum_comm]
  refine Finset.sum_congr rfl fun edge _ ↦ ?_
  have hSplit : ∀ raw : κ.data.SourceVertex,
      (if ρ raw = b then
        ((if (κ.data.sourceEnds edge).1 = raw then
            edgeSlope κ (chipSlope κ root anchor) edge else 0) -
          (if (κ.data.sourceEnds edge).2 = raw then
            edgeSlope κ (chipSlope κ root anchor) edge else 0)) else 0) =
        (if (κ.data.sourceEnds edge).1 = raw then
          (if ρ raw = b then edgeSlope κ (chipSlope κ root anchor) edge else 0) else 0) -
        (if (κ.data.sourceEnds edge).2 = raw then
          (if ρ raw = b then edgeSlope κ (chipSlope κ root anchor) edge else 0) else 0) := by
    intro raw
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun raw _ ↦ hSplit raw, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  split_ifs <;> ring

end Source

/-! ## 1c.  The row decomposition, by marked rows -/

section Rows

/-- **The row decomposition** (`PencilTransportProducer.sum_edges_eq_sum_rows`, marked): a
function on source edges vanishing on the dangling ones sums to the sum, over the core slots, of
its values along the frame's ordered **marked** rows. -/
theorem sum_edges_eq_sum_rows (g : κ.data.SourceEdge → ℤ)
    (hDangling : ∀ edge, IsDangling κ.data edge → g edge = 0) :
    (∑ edge : κ.data.SourceEdge, g edge) =
      ∑ e : Fin Q, ∑ i : Fin (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length,
        g (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i] := by
  classical
  have hOne : ∀ edge : κ.data.SourceEdge,
      g edge = ∑ e : Fin Q,
        if OnRow (markSet κ.markSource) (rowOf κ e) edge then g edge else 0 := by
    intro edge
    by_cases hD : IsDangling κ.data edge
    · rw [hDangling edge hD]
      simp
    · rw [Finset.sum_eq_single
        (κ.ident.row
          (markedRow (markSet κ.markSource) (⟨edge, hD⟩ : NonDanglingEdge κ.data)))]
      · rw [ite_eq_left ⟨hD, by rw [rowOf, Equiv.symm_apply_apply]⟩]
      · intro e _ hne
        rw [ite_eq_right]
        rintro ⟨hS, hPath⟩
        apply hne
        rw [hPath, rowOf, Equiv.apply_symm_apply]
      · simp
  rw [Finset.sum_congr rfl fun edge _ ↦ hOne edge, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hFilter : (∑ edge : κ.data.SourceEdge,
      if OnRow (markSet κ.markSource) (rowOf κ e) edge then g edge else 0) =
      ∑ edge ∈ (orderedRow κ.fullDim.pathEnds (rowOf κ e)).toFinset, g edge := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext edge
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    exact (mem_orderedRow_iff κ.fullDim.pathEnds _ edge).symm
  rw [hFilter, List.sum_toFinset _ (orderedRow_nodup κ.fullDim.pathEnds _)]
  exact (Fin.sum_univ_fun_getElem _ g).symm

end Rows

/-! ## 1d.  One row: offsets, slopes, and the row potential -/

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

variable (s : κ.target.edges → ℤ) (P : κ.target.V → ℤ)

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

/-- `rowSlope` reads the edge slope in the walk order
(`PencilTransportProducer.rowSlope_mul_sub`). -/
theorem rowSlope_mul_sub (e : Fin Q)
    (i : Fin (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length)
    (f : κ.data.SourceVertex → ℤ) :
    rowSlope κ s e i *
        (f (rowVertex κ.fullDim.pathEnds (rowOf κ e) i) -
          f (rowVertex κ.fullDim.pathEnds (rowOf κ e) (i.val + 1))) =
      edgeSlope κ s (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i] *
        (f (κ.data.sourceEnds (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]).1 -
          f (κ.data.sourceEnds (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]).2) := by
  have hSucc : rowVertex κ.fullDim.pathEnds (rowOf κ e) (i.val + 1) =
      otherEnd κ.data (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]
        (rowVertex κ.fullDim.pathEnds (rowOf κ e) i) :=
    rowVertex_succ κ.fullDim.pathEnds (rowOf κ e) i.isLt
  have hInc : Incident κ.data (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]
      (rowVertex κ.fullDim.pathEnds (rowOf κ e) i) :=
    rowVertex_incident κ.fullDim.pathEnds (rowOf κ e) i.isLt
  unfold rowSlope
  rw [hSucc]
  unfold otherEnd
  by_cases h : (κ.data.sourceEnds (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]).1 =
      rowVertex κ.fullDim.pathEnds (rowOf κ e) i
  · rw [ite_eq_left h, ite_eq_left h, h]
  · rw [ite_eq_right h, ite_eq_right h]
    have h2 : (κ.data.sourceEnds (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]).2 =
        rowVertex κ.fullDim.pathEnds (rowOf κ e) i := by
      rcases hInc with h1 | h1
      · exact absurd h1 h
      · exact h1
    rw [h2]
    ring

/-- Along one occurrence the pulled-back potential rises by the row slope times the realized
length. -/
theorem rowSlope_mul_rowLen (hRise : RiseCompatible y κ hClosed s P) (e : Fin Q)
    (i : Fin (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length) :
    rowSlope κ s e i * (rowLen y κ hClosed e i : ℤ) =
      sourcePotential κ P (rowVertex κ.fullDim.pathEnds (rowOf κ e) (i.val + 1)) -
        sourcePotential κ P (rowVertex κ.fullDim.pathEnds (rowOf κ e) i) := by
  have hSucc : rowVertex κ.fullDim.pathEnds (rowOf κ e) (i.val + 1) =
      otherEnd κ.data (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]
        (rowVertex κ.fullDim.pathEnds (rowOf κ e) i) :=
    rowVertex_succ κ.fullDim.pathEnds (rowOf κ e) i.isLt
  have hInc : Incident κ.data (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]
      (rowVertex κ.fullDim.pathEnds (rowOf κ e) i) :=
    rowVertex_incident κ.fullDim.pathEnds (rowOf κ e) i.isLt
  have hRise := sourcePotential_rise y κ hClosed s P hRise
    (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]
  unfold rowSlope rowLen
  rw [hSucc]
  unfold otherEnd
  by_cases h : (κ.data.sourceEnds (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]).1 =
      rowVertex κ.fullDim.pathEnds (rowOf κ e) i
  · rw [ite_eq_left h, ite_eq_left h, ← h, hRise]
  · rw [ite_eq_right h, ite_eq_right h]
    have h2 : (κ.data.sourceEnds (orderedRow κ.fullDim.pathEnds (rowOf κ e))[i]).2 =
        rowVertex κ.fullDim.pathEnds (rowOf κ e) i := by
      rcases hInc with h1 | h1
      · exact absurd h1 h
      · exact h1
    rw [← h2]
    linarith

/-- The potential telescopes along the whole row. -/
theorem sum_rowSlope_mul_rowLen (hRise : RiseCompatible y κ hClosed s P) (e : Fin Q) :
    (∑ i : Fin (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length,
      rowSlope κ s e i * (rowLen y κ hClosed e i : ℤ)) =
      sourcePotential κ P (rowVertex κ.fullDim.pathEnds (rowOf κ e)
          (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length) -
        sourcePotential κ P (rowVertex κ.fullDim.pathEnds (rowOf κ e) 0) := by
  rw [Finset.sum_congr rfl fun i _ ↦ rowSlope_mul_rowLen y κ hClosed s P hRise e i]
  exact Finset.sum_range_sub (fun j ↦ sourcePotential κ P
    (rowVertex κ.fullDim.pathEnds (rowOf κ e) j)) _ ▸
      (Fin.sum_univ_eq_sum_range (fun j ↦ sourcePotential κ P
        (rowVertex κ.fullDim.pathEnds (rowOf κ e) (j + 1)) -
        sourcePotential κ P (rowVertex κ.fullDim.pathEnds (rowOf κ e) j)) _)

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
  rw [pushed_apply, pushed_apply, ← Finset.sum_sub_distrib,
    ← sum_fibre_sub κ root anchor (realize D small hN hL k hk κ hClosed hScale) b]
  refine Finset.sum_congr rfl fun raw _ ↦ ?_
  by_cases hb : realize D small hN hL k hk κ hClosed hScale raw = b
  · rw [ite_eq_left hb, ite_eq_left hb, ite_eq_left hb]
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

/-- **The big-side script**: the pulled-back tree potential, read along every big slot through
the frame's own marked row. -/
noncomputable def script : firing_script (D.bigSpec (small.scale k hk) hN hL).graph :=
  (D.bigSpec (small.scale k hk) hN hL).slotValueScript (corePotential D κ P)
    (slotValue D small hN hL k hk κ hClosed s P)

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
  have hGe := fun e ↦ @RowAlgebra.value_of_ge _ _ _ _ _
    (rowStart_succ (degenerateLength D small) κ hClosed e) _
    (sum_rowSlope_mul_rowLen (degenerateLength D small) κ hClosed s P hRise e)
  constructor
  · intro e
    change _ = corePotential D κ P (D.bigCore.tail e)
    have hEnds := reverse_endpoints κ hL e
    unfold slotValue RowAlgebra.orient
    cases hr : reverse κ e
    · simp only [hr, Bool.false_eq_true, ite_false] at hEnds ⊢
      rw [RowAlgebra.value_of_nonpos _ _ _ _ (by simp), ← hEnds.1, corePotential_ident]
      rfl
    · simp only [hr, ite_true] at hEnds ⊢
      rw [hGe e (by have := hFull e; omega), ← hEnds.2, corePotential_ident]
      rfl
  · intro e
    change _ = corePotential D κ P (D.bigCore.head e)
    have hEnds := reverse_endpoints κ hL e
    unfold slotValue RowAlgebra.orient
    cases hr : reverse κ e
    · simp only [hr, Bool.false_eq_true, ite_false] at hEnds ⊢
      rw [hGe e (by have := hFull e; omega), ← hEnds.2, corePotential_ident]
      rfl
    · simp only [hr, ite_true] at hEnds ⊢
      rw [RowAlgebra.value_of_nonpos _ _ _ _ (by simp), ← hEnds.1, corePotential_ident]
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

include hN hL hk hScale in
/-- The core potential is constant on every fibre of `D.fib`: the fibre is connected through
contracted slots (the last clause of `ExpansionData.Conditions`). -/
theorem corePotential_eq_of_fib_eq
    (hRise : RiseCompatible (degenerateLength D small) κ hClosed s P)
    (hCond : D.Conditions small.core) {v w : Fin N} (h : D.fib v = D.fib w) :
    corePotential D κ P v = corePotential D κ P w := by
  classical
  by_contra hne
  obtain ⟨e, hc, -, hcross⟩ := ExpansionData.fibre_of_conditions hCond (D.fib v)
    (Finset.univ.filter fun u ↦ corePotential D κ P u = corePotential D κ P v)
    ⟨v, by simp, rfl⟩ ⟨w, by simpa using fun h' ↦ hne h'.symm, h.symm⟩
  have hEq := corePotential_contracted D small hN hL k hk κ hClosed hScale s P hRise e hc
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 (hEq.symm.trans h1)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 (hEq.trans h1)

include hScale in
/-- **The script descends**: it is constant on the fibres of the contraction. -/
theorem script_eq_of_vertexMap_eq
    (hRise : RiseCompatible (degenerateLength D small) κ hClosed s P)
    (hCond : D.Conditions small.core) {x x' : (D.bigSpec (small.scale k hk) hN hL).Vertex}
    (h : ExpansionData.vertexMap D (small.scale k hk) hN hL x =
      ExpansionData.vertexMap D (small.scale k hk) hN hL x') :
    script D small hN hL k hk κ hClosed s P x = script D small hN hL k hk κ hClosed s P x' := by
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  rcases x with v | ⟨e, o⟩
  · rcases x' with w | ⟨e', o'⟩
    · have hfib : D.fib v = D.fib w := by
        have h' : (small.scale k hk).coreVertex (D.fib v) =
            (small.scale k hk).coreVertex (D.fib w) := h
        exact Sum.inl.inj h'
      exact corePotential_eq_of_fib_eq D small hN hL k hk κ hClosed hScale s P hRise hCond hfib
    · rw [ExpansionData.interior_fibre hCond' e' o' _ h]
      rfl
  · rw [ExpansionData.interior_fibre hCond' e o x' h.symm]
    rfl

/-- The descended script on the small subdivision. -/
noncomputable def smallScript (hCond : D.Conditions small.core) :
    firing_script (small.scale k hk).graph := fun b ↦
  script D small hN hL k hk κ hClosed s P
    (Classical.choose (ExpansionData.vertexMap_surjective
      (D := D) (small := small.scale k hk) (hN := hN) (hL := hL) hCond b))

include hScale in
theorem script_eq_pullScript (hRise : RiseCompatible (degenerateLength D small) κ hClosed s P)
    (hCond : D.Conditions small.core) :
    script D small hN hL k hk κ hClosed s P =
      (ExpansionData.certificate D (small.scale k hk) hN hL).pullScript
        (smallScript D small hN hL k hk κ hClosed s P hCond) := by
  funext x
  exact script_eq_of_vertexMap_eq D small hN hL k hk κ hClosed hScale s P hRise hCond
    (Classical.choose_spec (ExpansionData.vertexMap_surjective
      (D := D) (small := small.scale k hk) (hN := hN) (hL := hL) hCond
      (ExpansionData.vertexMap D (small.scale k hk) hN hL x))).symm

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
local notation "BB" => D.bigSpec (small.scale k hk) hN hL
set_option hygiene false in
local notation "SV" => slotValue D small hN hL k hk κ hClosed (chipSlope κ root anchor)
  (chipPotential (degenerateLength D small) κ hClosed root anchor)
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
  rw [sum_edges_eq_sum_rows κ (fun edge ↦ edgeSlope κ (chipSlope κ root anchor) edge *
      ((if realize D small hN hL k hk κ hClosed hScale (κ.data.sourceEnds edge).1 = b
          then 1 else 0) -
        (if realize D small hN hL k hk κ hClosed hScale (κ.data.sourceEnds edge).2 = b
          then 1 else 0)))
    (fun edge hD ↦ by
      rw [realize_dangling D small hN hL k hk κ hClosed hScale hD]
      ring)]
  refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← rowSlope_mul_sub κ (chipSlope κ root anchor) e i (fun v ↦
    if realize D small hN hL k hk κ hClosed hScale v = b then 1 else 0)]
  unfold PencilTransportProducer.hit
  rw [realize_rowVertex D small hN hL k hk κ hClosed hScale hCond e i (le_of_lt i.isLt),
    realize_rowVertex D small hN hL k hk κ hClosed hScale hCond e (i.val + 1) i.isLt]

include hScale in
/-- **The big side of the identity**: the pushed Laplacian of the script, as a sum over the unit
steps of every big slot (`PencilTransportProducer.pushDiv_prin_script`). -/
theorem pushDiv_prin_script (hCond : D.Conditions small.core) (b : (small.scale k hk).Vertex) :
    (ExpansionData.certificate D (small.scale k hk) hN hL).pushDiv
        (prin (BB).graph
          (script D small hN hL k hk κ hClosed (chipSlope κ root anchor)
            (chipPotential (degenerateLength D small) κ hClosed root anchor))) b =
      ∑ e : Fin Q, ∑ o : Fin ((BB).length e),
        (SV e (o.val + 1) -
          SV e o.val) *
        (HIT e b o.val -
          HIT e b (o.val + 1)) := by
  classical
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  set B := BB
  have hSlope := B.isStepSlope_slotValueScript
    (compat D small hN hL k hk κ hClosed hScale (chipSlope κ root anchor)
      (chipPotential (degenerateLength D small) κ hClosed root anchor)
      (chip_riseCompatible (degenerateLength D small) κ hClosed root anchor))
  unfold GraphContractionCertificate.pushDiv
  simp only [script]
  rw [Finset.sum_congr rfl fun x _ ↦ by rw [B.prin_eq_sum_slopes hSlope x]]
  have hSwap : ∀ x : B.Vertex,
      (if (ExpansionData.certificate D (small.scale k hk) hN hL).vertexMap x = b then
        ∑ step : B.Step,
          ((if B.stepLeft step.1 step.2 = x then
              SV step.1 (step.2.val + 1) -
                SV step.1 step.2.val
            else 0) +
            (if B.stepRight step.1 step.2 = x then
              -(SV step.1 (step.2.val + 1) -
                SV step.1 step.2.val)
            else 0))
      else 0) =
        ∑ step : B.Step,
          ((if B.stepLeft step.1 step.2 = x then
              (if ExpansionData.vertexMap D (small.scale k hk) hN hL x = b then
                SV step.1 (step.2.val + 1) -
                  SV step.1 step.2.val
                else 0)
            else 0) +
            (if B.stepRight step.1 step.2 = x then
              (if ExpansionData.vertexMap D (small.scale k hk) hN hL x = b then
                -(SV step.1 (step.2.val + 1) -
                  SV step.1 step.2.val)
                else 0)
            else 0)) := by
    intro x
    by_cases hx : (ExpansionData.certificate D (small.scale k hk) hN hL).vertexMap x = b
    · rw [ite_eq_left hx]
      refine Finset.sum_congr rfl fun step _ ↦ ?_
      have hx' : ExpansionData.vertexMap D (small.scale k hk) hN hL x = b := hx
      simp only [hx', ite_true]
    · rw [ite_eq_right hx]
      have hx' : ¬ ExpansionData.vertexMap D (small.scale k hk) hN hL x = b := hx
      simp only [hx', ite_false, ite_self, add_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun x _ ↦ hSwap x, Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun o _ ↦ ?_
  rw [ExpansionData.vertexMap_stepLeft hCond' e o, ExpansionData.vertexMap_stepRight hCond' e o]
  unfold PencilTransportProducer.hit
  split_ifs <;> ring

include hScale in
/-- **(T), typed.** Any two pushed fibres of a closed typed frame are linearly equivalent on the
small subdivision: their difference is the Laplacian of the descended script
(`PencilTransportProducer.linear_equiv_pushDivisor`). -/
theorem linear_equiv_pushed (hCond : D.Conditions small.core) :
    linear_equiv (small.scale k hk).graph
      (pushed D small hN hL k hk κ hClosed hScale root)
      (pushed D small hN hL k hk κ hClosed hScale anchor) := by
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  unfold linear_equiv
  rw [principal_iff_eq_prin]
  refine ⟨smallScript D small hN hL k hk κ hClosed (chipSlope κ root anchor)
    (chipPotential (degenerateLength D small) κ hClosed root anchor) hCond, ?_⟩
  rw [← (ExpansionData.certificate D (small.scale k hk) hN hL).pushDiv_prin_pullScript
      (ExpansionData.certificate_valid hCond'),
    ← script_eq_pullScript D small hN hL k hk κ hClosed hScale (chipSlope κ root anchor)
      (chipPotential (degenerateLength D small) κ hClosed root anchor)
      (chip_riseCompatible (degenerateLength D small) κ hClosed root anchor) hCond]
  funext b
  rw [Pi.sub_apply, pushed_sub_eq_rows D small hN hL k hk κ hClosed hScale root anchor hCond b,
    pushDiv_prin_script D small hN hL k hk κ hClosed hScale root anchor hCond b]
  exact Finset.sum_congr rfl fun e _ ↦ (RowAlgebra.slot_sum _ _
    (rowStart_succ (degenerateLength D small) κ hClosed e) (reverse κ e) _
    (fun i ↦ (rowStart_add_rowLen_le (degenerateLength D small) κ hClosed e i).trans
      (rowStart_full_le_length D small hN hL k hk κ hClosed hScale e)) (HIT e b)).symm

end Compare

end DiagonalSecant.CTTransport
