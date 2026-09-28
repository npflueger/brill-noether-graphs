import DraismaVargasCount.CorePencilCoverProducer
import DraismaVargasCount.TreeMetricPotential

/-!
# The descent of the pencil: (T) `PencilTransport` and `DoubleRowInterior`

This module completes step 5 of `Assembly`, the descent of pencils to regular
subdivisions of odd order.  `CorePencilCoverProducer` reduces the last geometric
input of the endgame `CorePencilCoverProducer.witness_of_c34_and_markerFreePencilCover`,
namely `MarkerFreePencilCoverSupply`, to two statements through
`CorePencilCoverProducer.markerFreePencilCoverSupply_of_transport_doubleRowInterior`:
(T) `PencilTransport` and `DoubleRowInterior` (for loop doubles).  Both are proved
here, in general, and `markerFreePencilCoverSupply` is the result.

## (T): the pushed pencil is a linear system on the small subdivision

For target vertices `root`, `anchor` of the member's target tree take the integral
tree slope `TreeMetricPotential.chipSlope` (incidence `anchor - root`) and the potential
`TreeMetricPotential.chipPotential` integrating it against the member's **own realized
integral target lengths** (zeros allowed).  Pull the potential back to the source
(`sourcePotential`).  Along a source edge it rises by `edgeSlope * sourceLength`
(`sourcePotential_rise`, the dilation equation), and the sheet-partition refinement
equation `GluingDatum.sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence` says the
fibre difference is its signed incidence (`fibre_sub_eq`).  So:

* **small side** (`pushDivisor_sub_eq_rows`): the pushed difference
  `pushDivisor (bigDivisor anchor) - pushDivisor (bigDivisor root)` at a small vertex is a
  sum over source edges of `edgeSlope` times the difference of the end indicators
  (`sum_fibre_sub`); dangling edges contribute nothing (`realization_dangling`), the rest
  are the rows' occurrences (`sum_edges_eq_sum_rows`), and the realization of every row
  vertex is `kindVertex` at its own oriented offset (`realization_rowVertex`).
* **big side**: the script `script` on `D.bigSpec (small.scale k hk)` whose value at offset
  `o` of slot `e` is the row potential `rowValue` at the oriented position — the potential
  at the row's start plus the row slopes times clamped ramps `ramp` over the occurrences'
  windows.  It is compatible at both ends of every slot (`compat`), constant on contracted
  slots (whose occurrences have length zero) and hence on every fibre of the contraction
  (`script_eq_of_vertexMap_eq`, through the last clause of `ExpansionData.Conditions`), so it
  is a pulled-back script (`script_eq_pullScript`).  Its pushed Laplacian
  (`pushDiv_prin_script`) is, slot by slot, the same row sum (`slot_sum`: each occurrence
  telescopes over its window, `sum_window`; reversal maps windows to windows).
* `linear_equiv_pushDivisor` — the two agree, and `pushDiv_prin_pullScript` turns the
  big-side Laplacian into the small-side Laplacian of the descended script `smallScript`.
  Hence **`pencilTransport`**: `PencilTransport` at every root, from `D.Conditions small.core`
  alone.  No reduction to target edges (`pencilTransport_of_adjacent`) is needed.

## `DoubleRowInterior` for loop doubles

`doubleRowInterior_of_loopDoubles`.  The development above is stated for any integral
target potential whose rises are integral multiples of the realized lengths
(`RiseCompatible`).  For a loop double the two ends of the row carry labels in one
`D.fib`-fibre, so every such potential takes equal values at them (`corePotential_eq_of_fib_eq`).
If no interior row vertex lay strictly inside the chain, one occurrence would carry the
whole length and all others length zero; the potential rising only along that occurrence's
target edge (`TreeMetricPotential.integrate`) would then differ at the two ends.

## What is proved

§1 `ramp`, `ramp_succ_sub`, `ramp_of_le`, `ramp_of_ge`, `sum_window`; §2 `RiseCompatible`,
`chipSlope`, `chipPotential`, `chip_riseCompatible`, `sourcePotential`, `edgeSlope`,
`sourcePotential_rise`, `fibre_sub_eq`; §3 `sum_fibre_sub`, `sum_edges_eq_sum_rows`; §4 row
data (`rowStart`, `rowLen`, `rowSlope`, `rowValue` and their lemmas); §5 the realization
(`pushDivisor_sub_eq`, `realization_dangling`, `kindVertex_zero_eq`, `kindVertex_length_eq`,
`realization_branch_end`, `offsetVal_eq`, `realization_rowVertex`); §6 the script
(`slotPos`, `slotValue`, `corePotential`, `script`, `compat`, `corePotential_contracted`,
`corePotential_eq_of_fib_eq`, `script_eq_of_vertexMap_eq`, `smallScript`,
`script_eq_pullScript`); §7 `hit`, `pushDivisor_sub_eq_rows`, `pushDiv_prin_script`,
`slot_sum`, **`linear_equiv_pushDivisor`**; §8 **`pencilTransport`**,
**`doubleRowInterior_of_loopDoubles`**, `forestContractionRank_of_loopDoubles`; §9
**`markerFreePencilCoverSupply`**, the descent of step 5 of the genus-six assembly
(`DraismaVargas.Count.genusSix_witness`).

The one new `Prop`, `RiseCompatible` (the definition of "integral slope times realized
length" for a target potential), is not a hypothesis of any theorem of §8--§9; it is
inhabited by `chip_riseCompatible` and by the separating potential inside
`doubleRowInterior_of_loopDoubles`.

## What is NOT proved (every hypothesis, explicitly)

* `markerFreePencilCoverSupply` has no hypothesis.
* `pencilTransport` and `forestContractionRank_of_loopDoubles` take `D.Conditions small.core`
  (and the latter `LoopDoubles` and `small.core.Connected`, as
  `CorePencilCoverProducer` does).  `doubleRowInterior_of_loopDoubles` takes
  `LoopDoubles`; for a non-loop double it is not claimed (the docstring of
  `CorePencilCoverProducer` argues that it can fail there).
* **The big-side (T), `DegenerateFibreCover.FibreTransportFrom`, is not proved.**  The
  script here does *not* satisfy the big-side identity in general: on a contracted slot
  whose (zero-length) row lies over an edge of the `root`–`anchor` path, the row's last
  occurrence is placed across the unit slot.  The identity holds only after the
  contraction, which is all `PencilTransport` asks.  (This failure is argued from the
  placement, not formalized.)
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

namespace DraismaVargas.Count.PencilTransportProducer

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableGraphIncidence
open DraismaVargas.Count.DegenerateBigDivisor
open DraismaVargas.Count.DegenerateRealizationImage
open CanonicalSurvivor PendantRetraction RowRealizedPosition
open RowWalk RowPosition SurvivingSlotMap SlotMoment
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

/-! ## 1.  Ramps and their telescoping -/

section Ramp

/-- The clamped ramp `min (max (q - start) 0) len`. -/
def ramp (q start len : ℤ) : ℤ := min (max (q - start) 0) len

theorem ramp_succ_sub (o start len : ℤ) (hLen : 0 ≤ len) :
    ramp (o + 1) start len - ramp o start len =
      if start ≤ o ∧ o < start + len then 1 else 0 := by
  unfold ramp
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    rw [max_eq_left (by omega), max_eq_left (by omega), min_eq_left (by omega),
      min_eq_left (by omega)]
    ring
  · rcases not_and_or.mp h with h1 | h2
    · push Not at h1
      rw [max_eq_right (by omega), max_eq_right (by omega)]
      simp
    · push Not at h2
      rw [min_eq_right (by omega), min_eq_right (by omega)]
      ring

theorem ramp_of_le (q start len : ℤ) (hLen : 0 ≤ len) (hq : q ≤ start) :
    ramp q start len = 0 := by
  unfold ramp
  rw [max_eq_right (by omega), min_eq_left hLen]

theorem ramp_of_ge (q start len : ℤ) (hLen : 0 ≤ len) (hq : start + len ≤ q) :
    ramp q start len = len := by
  unfold ramp
  rw [max_eq_left (by omega), min_eq_right (by omega)]

/-- **Telescoping along a window.**  Summing the step differences of `δ` over the
unit steps of the window `[start, start + len)` leaves its two ends. -/
theorem sum_window (δ : ℕ → ℤ) (total start len : ℕ) (h : start + len ≤ total) :
    (∑ o ∈ Finset.range total,
      (if start ≤ o ∧ o < start + len then (1 : ℤ) else 0) * (δ o - δ (o + 1))) =
      δ start - δ (start + len) := by
  induction len with
  | zero =>
      rw [Finset.sum_eq_zero]
      · simp
      · intro o _
        rw [if_neg (by omega), zero_mul]
  | succ len ih =>
      have hSplit : ∀ o ∈ Finset.range total,
          (if start ≤ o ∧ o < start + (len + 1) then (1 : ℤ) else 0) * (δ o - δ (o + 1)) =
            (if start ≤ o ∧ o < start + len then (1 : ℤ) else 0) * (δ o - δ (o + 1)) +
              (if o = start + len then δ o - δ (o + 1) else 0) := by
        intro o _
        by_cases h1 : start ≤ o ∧ o < start + len
        · rw [if_pos ⟨h1.1, by omega⟩, if_pos h1, if_neg (by omega)]
          ring
        · by_cases h2 : o = start + len
          · rw [if_pos (by omega), if_neg h1, if_pos h2]
            ring
          · rw [if_neg (by omega), if_neg h1, if_neg h2]
            ring
      rw [Finset.sum_congr rfl hSplit, Finset.sum_add_distrib, ih (by omega),
        Finset.sum_ite_eq' (Finset.range total) (start + len)]
      rw [if_pos (Finset.mem_range.mpr (by omega))]
      rw [show start + (len + 1) = start + len + 1 by omega]
      ring

end Ramp

/-! ## 2.  The source side: the fibre difference is a pulled-back incidence -/

section Source

variable {n p degree : ℕ} {core : Utilities.Certificate.ExplicitPotential.Core n p}
  {y : Fin p → ℚ} (member : FibreMember core y degree) (hClosed : member.Closed)

/-- An integral potential on the target whose rise along every target edge is an
integral slope times the member's realized length of that edge.  Zero lengths are
allowed, and then the rise is zero. -/
def RiseCompatible (s : member.target.edges → ℤ) (P : member.target.V → ℤ) : Prop :=
  ∀ t : member.target.edges,
    P (t : member.target.V × member.target.V).2 - P (t : member.target.V × member.target.V).1 =
      s t * ((memberRealization member hClosed).targetLength t : ℤ)

/-- The integral tree slope with incidence `anchor - root`. -/
noncomputable def chipSlope (root anchor : member.target.V) : member.target.edges → ℤ :=
  TreeMetricPotential.chipSlope member.data member.fullDim.targetConnected
    member.fullDim.targetGenus root anchor

/-- The tree potential integrating `chipSlope` against the member's own realized
target lengths (zeros allowed). -/
noncomputable def chipPotential (root anchor : member.target.V) : member.target.V → ℤ :=
  TreeMetricPotential.chipPotential member.data member.fullDim.targetConnected
    member.fullDim.targetGenus (memberRealization member hClosed).targetLength root anchor

theorem chip_riseCompatible (root anchor : member.target.V) :
    RiseCompatible member hClosed (chipSlope member root anchor)
      (chipPotential member hClosed root anchor) := fun t ↦
  TreeMetricPotential.chipPotential_rise member.data member.fullDim.targetConnected
    member.fullDim.targetGenus (memberRealization member hClosed).targetLength root anchor t

variable (s : member.target.edges → ℤ) (P : member.target.V → ℤ)

/-- The pulled-back potential on the source. -/
def sourcePotential (x : member.data.SourceVertex) : ℤ := P x.1.1

/-- The slope of the pulled-back potential along one source edge, per unit of
its realized length. -/
def edgeSlope (edge : member.data.SourceEdge) : ℤ :=
  s edge.1.1 * (member.data.sourceEdgeIndex edge : ℤ)

theorem sourcePotential_rise (hRise : RiseCompatible member hClosed s P)
    (edge : member.data.SourceEdge) :
    sourcePotential member P (member.data.sourceEnds edge).2 -
        sourcePotential member P (member.data.sourceEnds edge).1 =
      edgeSlope member s edge *
        ((memberRealization member hClosed).sourceLength edge : ℤ) := by
  have h := hRise edge.1.1
  have hDil := (memberRealization member hClosed).dilation_length edge
  have hDilZ : ((member.data.sourceEdgeIndex edge : ℕ) : ℤ) *
      ((memberRealization member hClosed).sourceLength edge : ℤ) =
      ((memberRealization member hClosed).targetLength edge.1.1 : ℤ) := by
    exact_mod_cast hDil
  unfold sourcePotential edgeSlope
  change P (edge.1.1 : member.target.V × member.target.V).2 -
    P (edge.1.1 : member.target.V × member.target.V).1 = _
  rw [h, ← hDilZ]
  ring

/-- **The fibre difference is the pulled-back incidence.**  At every source
vertex the fibre over `anchor` minus the fibre over `root` is the signed sum of
the edge slopes at that vertex: the sheet-partition refinement equation
`sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence` against the tree
slope with incidence `anchor - root`. -/
theorem fibre_sub_eq (root anchor : member.target.V) (raw : member.data.SourceVertex) :
    ((if raw.1.1 = anchor then
        ((member.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0) -
      (if raw.1.1 = root then
        ((member.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0)) =
      ∑ edge : member.data.SourceEdge,
        ((if (member.data.sourceEnds edge).1 = raw then edgeSlope member (chipSlope member root anchor) edge
            else 0) -
          (if (member.data.sourceEnds edge).2 = raw then edgeSlope member (chipSlope member root anchor) edge
            else 0)) := by
  have h := member.data.sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence
    (chipSlope member root anchor) raw
  have hInc := TreeMetricPotential.chipSlope_incidence member.data
    member.fullDim.targetConnected member.fullDim.targetGenus root anchor raw.1.1
  unfold sourceEdgeIncidence at h
  change _ = ((member.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) *
    targetEdgeIncidence (chipSlope member root anchor) raw.1.1 at h
  unfold chipSlope at h
  rw [hInc] at h
  have hL : ∑ edge : member.data.SourceEdge,
      ((if (member.data.sourceEnds edge).1 = raw then edgeSlope member (chipSlope member root anchor) edge
          else 0) -
        (if (member.data.sourceEnds edge).2 = raw then edgeSlope member (chipSlope member root anchor) edge
          else 0)) =
      ∑ edge : member.data.SourceEdge,
        ((if (member.data.sourceEnds edge).1 = raw then
            (member.data.sourceEdgeIndex edge : ℤ) *
              TreeMetricPotential.chipSlope member.data member.fullDim.targetConnected
                member.fullDim.targetGenus root anchor edge.1.1 else 0) +
          (if (member.data.sourceEnds edge).2 = raw then
            (member.data.sourceEdgeIndex edge : ℤ) *
              -TreeMetricPotential.chipSlope member.data member.fullDim.targetConnected
                member.fullDim.targetGenus root anchor edge.1.1 else 0)) := by
    refine Finset.sum_congr rfl fun edge _ ↦ ?_
    unfold edgeSlope chipSlope
    split_ifs <;> ring
  rw [hL, h]
  split_ifs <;> ring

end Source

/-! ## 3.  Pushing the fibre difference along any map, and the row decomposition -/

section Push

variable {n p degree : ℕ} {core : Utilities.Certificate.ExplicitPotential.Core n p}
  {y : Fin p → ℚ} (member : FibreMember core y degree)
  (root anchor : member.target.V)

/-- **The pushed fibre difference, edge by edge.**  Along any map `ρ` out of the
source, the pushforward of `fibre anchor - fibre root` at `b` is the sum over
source edges of the edge slope times the difference of the two end indicators.
An edge with both ends over `b`, or neither, contributes nothing. -/
theorem sum_fibre_sub {X : Type*} [DecidableEq X] (ρ : member.data.SourceVertex → X) (b : X) :
    (∑ raw : member.data.SourceVertex,
      if ρ raw = b then
        ((if raw.1.1 = anchor then
            ((member.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0) -
          (if raw.1.1 = root then
            ((member.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0))
      else 0) =
      ∑ edge : member.data.SourceEdge, edgeSlope member (chipSlope member root anchor) edge *
        ((if ρ (member.data.sourceEnds edge).1 = b then 1 else 0) -
          (if ρ (member.data.sourceEnds edge).2 = b then 1 else 0)) := by
  classical
  have hStep : ∀ raw : member.data.SourceVertex,
      (if ρ raw = b then
        ((if raw.1.1 = anchor then
            ((member.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0) -
          (if raw.1.1 = root then
            ((member.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0))
      else 0) =
        ∑ edge : member.data.SourceEdge,
          (if ρ raw = b then
            ((if (member.data.sourceEnds edge).1 = raw then
                edgeSlope member (chipSlope member root anchor) edge else 0) -
              (if (member.data.sourceEnds edge).2 = raw then
                edgeSlope member (chipSlope member root anchor) edge else 0)) else 0) := by
    intro raw
    by_cases hb : ρ raw = b
    · simp only [if_pos hb]
      exact fibre_sub_eq member root anchor raw
    · simp only [if_neg hb, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun raw _ ↦ hStep raw, Finset.sum_comm]
  refine Finset.sum_congr rfl fun edge _ ↦ ?_
  have hSplit : ∀ raw : member.data.SourceVertex,
      (if ρ raw = b then
        ((if (member.data.sourceEnds edge).1 = raw then
            edgeSlope member (chipSlope member root anchor) edge else 0) -
          (if (member.data.sourceEnds edge).2 = raw then
            edgeSlope member (chipSlope member root anchor) edge else 0)) else 0) =
        (if (member.data.sourceEnds edge).1 = raw then
          (if ρ raw = b then edgeSlope member (chipSlope member root anchor) edge else 0) else 0) -
        (if (member.data.sourceEnds edge).2 = raw then
          (if ρ raw = b then edgeSlope member (chipSlope member root anchor) edge else 0) else 0) := by
    intro raw
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun raw _ ↦ hSplit raw, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  split_ifs <;> ring

end Push

section Rows

variable {n p degree : ℕ} {core : Utilities.Certificate.ExplicitPotential.Core n p}
  {y : Fin p → ℚ} (member : FibreMember core y degree)

/-- **The row decomposition.**  A function on source edges vanishing on the
dangling ones sums to the sum, over the core slots, of its values along the
member's ordered rows. -/
theorem sum_edges_eq_sum_rows (g : member.data.SourceEdge → ℤ)
    (hDangling : ∀ edge, IsDangling member.data edge → g edge = 0) :
    (∑ edge : member.data.SourceEdge, g edge) =
      ∑ e : Fin p, ∑ i : Fin (orderedRow member.fullDim.pathEnds
          (member.ident.row.symm e)).length,
        g (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i] := by
  classical
  -- Step 1: each surviving edge lies on exactly one stable row.
  have hOne : ∀ edge : member.data.SourceEdge,
      g edge = ∑ path : StablePath member.data,
        if OnRow member.data path edge then g edge else 0 := by
    intro edge
    by_cases hD : IsDangling member.data edge
    · rw [hDangling edge hD]
      simp
    · rw [Finset.sum_eq_single (NonDanglingEdge.stablePath (⟨edge, hD⟩ : NonDanglingEdge member.data))]
      · rw [if_pos ⟨hD, rfl⟩]
      · intro path _ hne
        rw [if_neg]
        rintro ⟨hS, hPath⟩
        exact hne hPath.symm
      · simp
  rw [Finset.sum_congr rfl fun edge _ ↦ hOne edge, Finset.sum_comm]
  rw [← (member.ident.row.symm).sum_comp]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hFilter : (∑ edge : member.data.SourceEdge,
      if OnRow member.data (member.ident.row.symm e) edge then g edge else 0) =
      ∑ edge ∈ (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).toFinset,
        g edge := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext edge
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    exact (mem_orderedRow_iff member.fullDim.pathEnds _ edge).symm
  rw [hFilter, List.sum_toFinset _ (orderedRow_nodup member.fullDim.pathEnds _)]
  exact (Fin.sum_univ_fun_getElem _ g).symm

end Rows

/-! ## 4.  One row: offsets, slopes, and the row potential -/

section RowData

variable {n p degree : ℕ} {core : Utilities.Certificate.ExplicitPotential.Core n p}
  {y : Fin p → ℚ} (member : FibreMember core y degree) (hClosed : member.Closed)
  (s : member.target.edges → ℤ) (P : member.target.V → ℤ)

/-- The integral offset, from the row's start, of the `i`-th row vertex. -/
noncomputable def rowStart (e : Fin p) (i : ℕ) : ℕ :=
  integralPrefix member.fullDim (memberRealization member hClosed) (member.ident.row.symm e) i

/-- The realized integral length of the `i`-th occurrence of the row. -/
noncomputable def rowLen (e : Fin p)
    (i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length) : ℕ :=
  (memberRealization member hClosed).sourceLength
    (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]

/-- The slope of the pulled-back potential along the `i`-th occurrence, read in
the row's own direction. -/
noncomputable def rowSlope (e : Fin p)
    (i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length) : ℤ :=
  if (member.data.sourceEnds (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]).1 =
      rowVertex member.fullDim (member.ident.row.symm e) i then
    edgeSlope member s (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]
  else
    -edgeSlope member s (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]

theorem rowStart_succ (e : Fin p)
    (i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length) :
    rowStart member hClosed e (i.val + 1) =
      rowStart member hClosed e i + rowLen member hClosed e i := by
  unfold rowStart rowLen integralPrefix
  rw [List.take_add_one, List.getElem?_eq_getElem i.isLt]
  simp

theorem rowStart_zero (e : Fin p) : rowStart member hClosed e 0 = 0 := by
  simp [rowStart, integralPrefix]

theorem rowStart_le_full (e : Fin p) (j : ℕ) :
    rowStart member hClosed e j ≤ rowStart member hClosed e
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length :=
  RowSlotMap.integralPrefix_le_full member.fullDim (memberRealization member hClosed) _ j

theorem rowStart_add_rowLen_le (e : Fin p)
    (i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length) :
    rowStart member hClosed e i + rowLen member hClosed e i ≤ rowStart member hClosed e
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length := by
  rw [← rowStart_succ]
  exact rowStart_le_full member hClosed e _

/-- The two ends of the `i`-th occurrence are the `i`-th and `(i+1)`-st row
vertices, and `rowSlope` reads the edge slope in that order: for any function
`f` on source vertices, the signed differences agree. -/
theorem rowSlope_mul_sub (e : Fin p)
    (i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length)
    (f : member.data.SourceVertex → ℤ) :
    rowSlope member s e i *
        (f (rowVertex member.fullDim (member.ident.row.symm e) i) -
          f (rowVertex member.fullDim (member.ident.row.symm e) (i.val + 1))) =
      edgeSlope member s (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i] *
        (f (member.data.sourceEnds
            (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]).1 -
          f (member.data.sourceEnds
            (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]).2) := by
  have hSucc : rowVertex member.fullDim (member.ident.row.symm e) (i.val + 1) =
      otherEnd member.data (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]
        (rowVertex member.fullDim (member.ident.row.symm e) i) :=
    OrientedTraversal.walkVertex_succ _ _ i.isLt
  have hInc := RowPosition.rowVertex_incident member.fullDim (member.ident.row.symm e) i.isLt
  unfold rowSlope
  rw [hSucc]
  unfold otherEnd
  by_cases h : (member.data.sourceEnds
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]).1 =
      rowVertex member.fullDim (member.ident.row.symm e) i
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h]
    have h2 : (member.data.sourceEnds
        (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]).2 =
        rowVertex member.fullDim (member.ident.row.symm e) i := by
      rcases hInc with h1 | h1
      · exact absurd h1 h
      · exact h1
    rw [h2]
    ring

/-- Along one occurrence the pulled-back potential rises by the row slope times
the realized length. -/
theorem rowSlope_mul_rowLen (hRise : RiseCompatible member hClosed s P) (e : Fin p)
    (i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length) :
    rowSlope member s e i * (rowLen member hClosed e i : ℤ) =
      sourcePotential member P
          (rowVertex member.fullDim (member.ident.row.symm e) (i.val + 1)) -
        sourcePotential member P
          (rowVertex member.fullDim (member.ident.row.symm e) i) := by
  have hSucc : rowVertex member.fullDim (member.ident.row.symm e) (i.val + 1) =
      otherEnd member.data (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]
        (rowVertex member.fullDim (member.ident.row.symm e) i) :=
    OrientedTraversal.walkVertex_succ _ _ i.isLt
  have hInc := RowPosition.rowVertex_incident member.fullDim (member.ident.row.symm e) i.isLt
  have hRise := sourcePotential_rise member hClosed s P hRise
    (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]
  unfold rowSlope rowLen
  rw [hSucc]
  unfold otherEnd
  by_cases h : (member.data.sourceEnds
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]).1 =
      rowVertex member.fullDim (member.ident.row.symm e) i
  · rw [if_pos h, if_pos h, ← h, hRise]
  · rw [if_neg h, if_neg h]
    have h2 : (member.data.sourceEnds
        (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i]).2 =
        rowVertex member.fullDim (member.ident.row.symm e) i := by
      rcases hInc with h1 | h1
      · exact absurd h1 h
      · exact h1
    rw [← h2]
    linarith

/-- The potential telescopes along the whole row. -/
theorem sum_rowSlope_mul_rowLen (hRise : RiseCompatible member hClosed s P) (e : Fin p) :
    (∑ i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length,
      rowSlope member s e i * (rowLen member hClosed e i : ℤ)) =
      sourcePotential member P
          (rowVertex member.fullDim (member.ident.row.symm e)
            (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length) -
        sourcePotential member P
          (rowVertex member.fullDim (member.ident.row.symm e) 0) := by
  rw [Finset.sum_congr rfl fun i _ ↦ rowSlope_mul_rowLen member hClosed s P hRise e i]
  exact Finset.sum_range_sub (fun j ↦ sourcePotential member P
    (rowVertex member.fullDim (member.ident.row.symm e) j)) _ ▸
      (Fin.sum_univ_eq_sum_range (fun j ↦ sourcePotential member P
        (rowVertex member.fullDim (member.ident.row.symm e) (j + 1)) -
        sourcePotential member P
          (rowVertex member.fullDim (member.ident.row.symm e) j)) _)

/-- The occurrence lengths add up to the full prefix. -/
theorem sum_rowLen (e : Fin p) :
    (∑ i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length,
      (rowLen member hClosed e i : ℤ)) =
      rowStart member hClosed e (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length := by
  have h : ∀ i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length,
      (rowLen member hClosed e i : ℤ) =
        (rowStart member hClosed e (i.val + 1) : ℤ) - (rowStart member hClosed e i : ℤ) := by
    intro i
    rw [rowStart_succ]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ h i]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ (rowStart member hClosed e (j + 1) : ℤ) -
    (rowStart member hClosed e j : ℤ)),
    Finset.sum_range_sub (fun j ↦ (rowStart member hClosed e j : ℤ)), rowStart_zero]
  simp

/-- **The row potential** at an integral position `pos` from the row's start. -/
noncomputable def rowValue (e : Fin p) (pos : ℤ) : ℤ :=
  sourcePotential member P (rowVertex member.fullDim (member.ident.row.symm e) 0) +
    ∑ i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length,
      rowSlope member s e i *
        ramp pos (rowStart member hClosed e i) (rowLen member hClosed e i)

theorem rowValue_of_nonpos (e : Fin p) {pos : ℤ} (hpos : pos ≤ 0) :
    rowValue member hClosed s P e pos =
      sourcePotential member P (rowVertex member.fullDim (member.ident.row.symm e) 0) := by
  unfold rowValue
  rw [Finset.sum_eq_zero, add_zero]
  intro i _
  have h0 : (0 : ℤ) ≤ rowStart member hClosed e i := by positivity
  rw [ramp_of_le _ _ _ (by positivity) (by omega), mul_zero]

theorem rowValue_of_ge (hRise : RiseCompatible member hClosed s P) (e : Fin p) {pos : ℤ}
    (hpos : (rowStart member hClosed e
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length : ℤ) ≤ pos) :
    rowValue member hClosed s P e pos =
      sourcePotential member P
        (rowVertex member.fullDim (member.ident.row.symm e)
          (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length) := by
  unfold rowValue
  rw [Finset.sum_congr rfl fun i _ ↦ by
    rw [ramp_of_ge _ _ _ (by positivity) (by
      have := rowStart_add_rowLen_le member hClosed e i
      have : ((rowStart member hClosed e i + rowLen member hClosed e i : ℕ) : ℤ) ≤ pos :=
        le_trans (by exact_mod_cast this) hpos
      push_cast at this
      omega)]]
  rw [sum_rowSlope_mul_rowLen member hClosed s P hRise]
  ring

end RowData

/-! ## 5.  The member's realization on the small subdivision, row by row -/

section Realization

variable {n p N Q degree : ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)

/-- **The pushed pencil difference, edge by edge.** -/
theorem pushDivisor_sub_eq (root anchor : member.target.V) (b : (small.scale k hk).Vertex) :
    ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale anchor) b -
      ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root) b =
      ∑ edge : member.data.SourceEdge, edgeSlope member (chipSlope member root anchor) edge *
        ((if CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale
            (member.data.sourceEnds edge).1 = b then 1 else 0) -
          (if CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale
            (member.data.sourceEnds edge).2 = b then 1 else 0)) := by
  classical
  rw [pushDivisor_bigDivisor, pushDivisor_bigDivisor, PendantDivisorTransport.push_apply,
    PendantDivisorTransport.push_apply, ← Finset.sum_sub_distrib]
  rw [← sum_fibre_sub member root anchor
    (CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale) b]
  refine Finset.sum_congr rfl fun raw _ ↦ ?_
  show (if CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale raw = b
      then _ else 0) - (if CorePencilCoverProducer.realization D small hN hL k hk member hClosed
        hScale raw = b then _ else 0) = _
  by_cases hb : CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale
      raw = b
  · rw [if_pos hb, if_pos hb, if_pos hb]
    rfl
  · rw [if_neg hb, if_neg hb, if_neg hb]
    ring

/-- A dangling edge is collapsed by the realization. -/
theorem realization_dangling {edge : member.data.SourceEdge}
    (hD : IsDangling member.data edge) :
    CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale
        (member.data.sourceEnds edge).1 =
      CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale
        (member.data.sourceEnds edge).2 := by
  have hRetract : retractVertex (member.data.sourceEnds edge).1 =
      retractVertex (member.data.sourceEnds edge).2 :=
    Quotient.sound (Relation.ReflTransGen.single ⟨edge, hD, Or.inl rfl⟩)
  exact congrArg (ExpansionData.vertexMap D (small.scale k hk) hN hL)
    (DegeneratePlacement.sourcePoint_of_retract (D.bigSpec (small.scale k hk) hN hL)
      (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale)
      hRetract)

include hN hL in
/-- `kindVertex` at offset `0` is the fibre of the slot's tail. -/
theorem kindVertex_zero_eq (hCond : D.Conditions small.core) (e : Fin Q) :
    kindVertex (small.scale k hk) (D.fib (D.bigCore.tail e)) (D.kind e) 0 =
      (small.scale k hk).coreVertex (D.fib (D.bigCore.tail e)) := by
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  have h := ExpansionData.vertexMap_pathVertex (D := D) (small := small.scale k hk)
    (hN := hN) (hL := hL) hCond' e ⟨0, by omega⟩
  rw [PathHelpers.pathVertex_of_zero _ e _ rfl] at h
  exact h.symm

/-- `kindVertex` at the full big length is the fibre of the slot's head. -/
theorem kindVertex_length_eq (hCond : D.Conditions small.core) (e : Fin Q) :
    kindVertex (small.scale k hk) (D.fib (D.bigCore.tail e)) (D.kind e)
        ((D.bigSpec (small.scale k hk) hN hL).length e) =
      (small.scale k hk).coreVertex (D.fib (D.bigCore.head e)) := by
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  have hPos := (D.bigSpec (small.scale k hk) hN hL).length_pos e
  have h := ExpansionData.vertexMap_pathVertex (D := D) (small := small.scale k hk)
    (hN := hN) (hL := hL) hCond' e ⟨(D.bigSpec (small.scale k hk) hN hL).length e, by omega⟩
  rw [PathHelpers.pathVertex_of_last _ e _ (by simp; omega) rfl] at h
  exact h.symm

/-- The member realizes a branch vertex labelled by an end of `e`, placed at that
end, as `kindVertex` there. -/
theorem realization_branch_end (hCond : D.Conditions small.core) (e : Fin Q)
    (branch : BranchVertex member.data) (rev : Bool)
    (hLabel : member.ident.vertex branch =
      if rev then D.bigCore.head e else D.bigCore.tail e) :
    CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale branch.1 =
      kindVertex (small.scale k hk) (D.fib (D.bigCore.tail e)) (D.kind e)
        (if rev then (D.bigSpec (small.scale k hk) hN hL).length e else 0) := by
  have h := vertexMap_sourcePoint_branch D small hN hL k hk member hClosed hScale branch
  refine h.trans ?_
  rw [hLabel]
  cases rev
  · simp only [Bool.false_eq_true, if_false]
    exact (kindVertex_zero_eq D small hN hL k hk hCond e).symm
  · simp only [if_true]
    exact (kindVertex_length_eq D small hN hL k hk hCond e).symm

/-- The prefix at `0` is `0`. -/
theorem integralPrefix_zero' (path : StablePath member.data) :
    integralPrefix member.fullDim (memberRealization member hClosed) path 0 = 0 := by
  simp [integralPrefix]

include hScale in
/-- The full prefix of a non-contracted slot is its big length. -/
theorem integralPrefix_full_of_ne (e : Fin Q) (hne : D.kind e ≠ SlotKind.contracted) :
    integralPrefix member.fullDim (memberRealization member hClosed)
        (member.ident.row.symm e)
        (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length =
      (D.bigSpec (small.scale k hk) hN hL).length e := by
  rw [member_integralPrefix_full (degenerateLength D small) member hClosed e, hScale,
    degenerateLength_of_ne D small hne]
  show k * kindLength small (D.kind e) = kindLength (small.scale k hk) (D.kind e)
  rw [kindLength_scale_of_ne_contracted small k hk hne]

/-- The full prefix of a contracted slot is `0`. -/
theorem integralPrefix_full_of_contracted (e : Fin Q) (hc : D.kind e = SlotKind.contracted) :
    integralPrefix member.fullDim (memberRealization member hClosed)
        (member.ident.row.symm e)
        (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length = 0 := by
  rw [member_integralPrefix_full (degenerateLength D small) member hClosed e,
    degenerateLength_contracted D small hc, Nat.mul_zero]

/-- `offsetVal`, in terms of `rowStart`. -/
theorem offsetVal_eq (e : Fin Q) (j : ℕ) :
    DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed e j =
      if DegeneratePlacement.reverse member e then
        (D.bigSpec (small.scale k hk) hN hL).length e - rowStart member hClosed e j
      else rowStart member hClosed e j := rfl

/-- **Every row vertex is realized at its own oriented offset.**  For every slot
`e` and every `j` up to the row length, the realization of the `j`-th vertex of
the member's row over `e` is `kindVertex` at `offsetVal e j`.  At the two ends
this is the branch placement; on a contracted slot `kindVertex` is constant and
the two ends lie in one fibre. -/
theorem realization_rowVertex (hCond : D.Conditions small.core) (e : Fin Q) (j : ℕ)
    (hj : j ≤ (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length) :
    CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale
        (rowVertex member.fullDim (member.ident.row.symm e) j) =
      kindVertex (small.scale k hk) (D.fib (D.bigCore.tail e)) (D.kind e)
        (DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member hClosed e j) := by
  have hEnds := DegeneratePlacement.reverse_endpoints hL member e
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- the start branch
    have h := realization_branch_end D small hN hL k hk member hClosed hScale hCond e
      (RowSlotOrientation.startBranch member.fullDim (member.ident.row.symm e))
      (DegeneratePlacement.reverse member e) hEnds.1
    refine h.trans ?_
    rw [offsetVal_eq, rowStart_zero]
    cases DegeneratePlacement.reverse member e <;> rfl
  by_cases hjl : j = (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length
  · -- the finish branch
    subst hjl
    have h := realization_branch_end D small hN hL k hk member hClosed hScale hCond e
      (RowSlotOrientation.finishBranch member.fullDim (member.ident.row.symm e))
      (!DegeneratePlacement.reverse member e)
      (by rw [hEnds.2]; cases DegeneratePlacement.reverse member e <;> rfl)
    by_cases hc : D.kind e = SlotKind.contracted
    · have hFib := (ExpansionData.compatible_of_conditions hCond e).1 hc
      have hv := vertexMap_sourcePoint_branch D small hN hL k hk member hClosed hScale
        (RowSlotOrientation.finishBranch member.fullDim (member.ident.row.symm e))
      refine hv.trans ?_
      rw [hc, hEnds.2]
      show _ = (small.scale k hk).coreVertex (D.fib (D.bigCore.tail e))
      split_ifs
      · rfl
      · rw [hFib]
    · refine h.trans ?_
      have hP : rowStart member hClosed e
          (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length =
          (D.bigSpec (small.scale k hk) hN hL).length e :=
        integralPrefix_full_of_ne D small hN hL k hk member hClosed hScale e hc
      rw [offsetVal_eq, hP]
      cases DegeneratePlacement.reverse member e <;> simp
  · -- an interior address
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h := vertexMap_sourcePoint_address D small hN hL k hk member hClosed hScale hCond
      ⟨member.ident.row.symm e, ⟨i, by omega⟩⟩
    simp only [Equiv.apply_symm_apply] at h
    exact h

end Realization

/-! ## 6.  The big-side script, its descent, and the transport -/

section Script

variable {n p N Q degree : ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)
  (s : member.target.edges → ℤ) (P : member.target.V → ℤ)

/-- The row position of the big-slot offset `o`, oriented by the row. -/
noncomputable def slotPos (e : Fin Q) (o : ℕ) : ℤ :=
  if DegeneratePlacement.reverse member e then
    ((D.bigSpec (small.scale k hk) hN hL).length e : ℤ) - o
  else o

/-- The script's value at offset `o` of big slot `e`. -/
noncomputable def slotValue (e : Fin Q) (o : ℕ) : ℤ :=
  rowValue member hClosed s P e (slotPos D small hN hL k hk member e o)

/-- The script's value at a big core vertex: the pulled-back potential at the
branch vertex carrying that label. -/
noncomputable def corePotential (v : Fin N) : ℤ :=
  sourcePotential member P (member.ident.vertex.symm v).1

/-- **The big-side script**: the pulled-back tree potential, read along every
big slot through the member's own row. -/
noncomputable def script : firing_script (D.bigSpec (small.scale k hk) hN hL).graph :=
  (D.bigSpec (small.scale k hk) hN hL).slotValueScript
    (corePotential D small member P)
    (slotValue D small hN hL k hk member hClosed s P)

theorem corePotential_ident (branch : BranchVertex member.data) :
    corePotential D small member P (member.ident.vertex branch) =
      sourcePotential member P branch.1 := by
  simp [corePotential]

include hScale in
theorem rowStart_full_le_length (e : Fin Q) :
    rowStart member hClosed e (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length ≤
      (D.bigSpec (small.scale k hk) hN hL).length e := by
  by_cases hc : D.kind e = SlotKind.contracted
  · have h := integralPrefix_full_of_contracted D small member hClosed e hc
    unfold rowStart
    rw [h]
    exact Nat.zero_le _
  · exact (integralPrefix_full_of_ne D small hN hL k hk member hClosed hScale e hc).le

include hScale in
/-- The script is compatible with the core potential at both ends of every slot. -/
theorem compat (hRise : RiseCompatible member hClosed s P) :
    (D.bigSpec (small.scale k hk) hN hL).SlotValueCompatible
      (corePotential D small member P)
      (slotValue D small hN hL k hk member hClosed s P) := by
  have hFull := rowStart_full_le_length D small hN hL k hk member hClosed hScale
  constructor
  · intro e
    change _ = corePotential D small member P (D.bigCore.tail e)
    have hEnds := DegeneratePlacement.reverse_endpoints hL member e
    unfold slotValue slotPos
    cases hr : DegeneratePlacement.reverse member e
    · simp only [hr, Bool.false_eq_true, if_false] at hEnds ⊢
      rw [rowValue_of_nonpos _ _ _ _ _ (by simp), ← hEnds.1, corePotential_ident]
      rfl
    · simp only [hr, if_true] at hEnds ⊢
      rw [rowValue_of_ge _ _ _ _ hRise _ (by have := hFull e; omega), ← hEnds.2,
        corePotential_ident]
      rfl
  · intro e
    change _ = corePotential D small member P (D.bigCore.head e)
    have hEnds := DegeneratePlacement.reverse_endpoints hL member e
    unfold slotValue slotPos
    cases hr : DegeneratePlacement.reverse member e
    · simp only [hr, Bool.false_eq_true, if_false] at hEnds ⊢
      rw [rowValue_of_ge _ _ _ _ hRise _ (by have := hFull e; omega), ← hEnds.2,
        corePotential_ident]
      rfl
    · simp only [hr, if_true] at hEnds ⊢
      rw [rowValue_of_nonpos _ _ _ _ _ (by simp), ← hEnds.1, corePotential_ident]
      rfl

/-- On a contracted slot every occurrence has length zero, so the row potential
is constant. -/
theorem rowValue_contracted (e : Fin Q) (hc : D.kind e = SlotKind.contracted) (pos : ℤ) :
    rowValue member hClosed s P e pos =
      sourcePotential member P
        (rowVertex member.fullDim (member.ident.row.symm e) 0) := by
  unfold rowValue
  rw [Finset.sum_eq_zero, add_zero]
  intro i _
  have h := rowStart_add_rowLen_le member hClosed e i
  have h0 := integralPrefix_full_of_contracted D small member hClosed e hc
  have hLen : rowLen member hClosed e i = 0 := by
    unfold rowStart at h
    rw [h0] at h
    omega
  rw [hLen, Nat.cast_zero]
  unfold ramp
  rw [min_eq_right (le_max_right _ _), mul_zero]

include hN hL hk hScale in
/-- The two ends of a contracted slot carry the same core potential. -/
theorem corePotential_contracted (hRise : RiseCompatible member hClosed s P) (e : Fin Q) (hc : D.kind e = SlotKind.contracted) :
    corePotential D small member P (D.bigCore.tail e) =
      corePotential D small member P (D.bigCore.head e) := by
  have hC := compat D small hN hL k hk member hClosed hScale s P hRise
  have h1 : corePotential D small member P (D.bigCore.tail e) =
      slotValue D small hN hL k hk member hClosed s P e 0 := (hC.tail e).symm
  have h2 : corePotential D small member P (D.bigCore.head e) =
      slotValue D small hN hL k hk member hClosed s P e
        ((D.bigSpec (small.scale k hk) hN hL).length e) := (hC.head e).symm
  rw [h1, h2]
  unfold slotValue
  rw [rowValue_contracted D small member hClosed s P e hc,
    rowValue_contracted D small member hClosed s P e hc]

include hN hL hk hScale in
/-- The core potential is constant on every fibre of `D.fib`: the fibre is
connected through contracted slots (the last clause of `ExpansionData.Conditions`). -/
theorem corePotential_eq_of_fib_eq (hRise : RiseCompatible member hClosed s P) (hCond : D.Conditions small.core) {v w : Fin N}
    (h : D.fib v = D.fib w) :
    corePotential D small member P v = corePotential D small member P w := by
  classical
  by_contra hne
  obtain ⟨e, hc, -, hcross⟩ := ExpansionData.fibre_of_conditions hCond (D.fib v)
    (Finset.univ.filter fun u ↦ corePotential D small member P u =
      corePotential D small member P v)
    ⟨v, by simp, rfl⟩ ⟨w, by simpa using fun h' ↦ hne h'.symm, h.symm⟩
  have hEq := corePotential_contracted D small hN hL k hk member hClosed hScale s P hRise e hc
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 (hEq.symm.trans h1)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 (hEq.trans h1)

include hScale in
/-- **The script descends**: it is constant on the fibres of the contraction. -/
theorem script_eq_of_vertexMap_eq (hRise : RiseCompatible member hClosed s P) (hCond : D.Conditions small.core)
    {x x' : (D.bigSpec (small.scale k hk) hN hL).Vertex}
    (h : ExpansionData.vertexMap D (small.scale k hk) hN hL x =
      ExpansionData.vertexMap D (small.scale k hk) hN hL x') :
    script D small hN hL k hk member hClosed s P x =
      script D small hN hL k hk member hClosed s P x' := by
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  rcases x with v | ⟨e, o⟩
  · rcases x' with w | ⟨e', o'⟩
    · have hfib : D.fib v = D.fib w := by
        have h' : (small.scale k hk).coreVertex (D.fib v) =
            (small.scale k hk).coreVertex (D.fib w) := h
        exact Sum.inl.inj h'
      exact corePotential_eq_of_fib_eq D small hN hL k hk member hClosed hScale s P hRise
        hCond hfib
    · rw [ExpansionData.interior_fibre hCond' e' o' _ h]
      rfl
  · rw [ExpansionData.interior_fibre hCond' e o x' h.symm]
    rfl

/-- The descended script on the small subdivision. -/
noncomputable def smallScript (hCond : D.Conditions small.core) :
    firing_script (small.scale k hk).graph := fun b ↦
  script D small hN hL k hk member hClosed s P
    (Classical.choose (ExpansionData.vertexMap_surjective
      (D := D) (small := small.scale k hk) (hN := hN) (hL := hL) hCond b))

include hScale in
theorem script_eq_pullScript (hRise : RiseCompatible member hClosed s P) (hCond : D.Conditions small.core) :
    script D small hN hL k hk member hClosed s P =
      (ExpansionData.certificate D (small.scale k hk) hN hL).pullScript
        (smallScript D small hN hL k hk member hClosed s P hCond) := by
  funext x
  exact script_eq_of_vertexMap_eq D small hN hL k hk member hClosed hScale s P hRise hCond
    (Classical.choose_spec (ExpansionData.vertexMap_surjective
      (D := D) (small := small.scale k hk) (hN := hN) (hL := hL) hCond
      (ExpansionData.vertexMap D (small.scale k hk) hN hL x))).symm

end Script

/-! ## 7.  Both sides, slot by slot -/

section Compare

variable {n p N Q degree : ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)
  (root anchor : member.target.V)

/-- The indicator of the small vertex `b` along the `kindVertex` path of `e`. -/
noncomputable def hit (e : Fin Q) (b : (small.scale k hk).Vertex) (q : ℕ) : ℤ :=
  if kindVertex (small.scale k hk) (D.fib (D.bigCore.tail e)) (D.kind e) q = b then 1 else 0

include hScale in
/-- **The small side of the identity**: the pushed pencil difference, as a sum
over the member's rows. -/
theorem pushDivisor_sub_eq_rows (hCond : D.Conditions small.core)
    (b : (small.scale k hk).Vertex) :
    ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale anchor) b -
      ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root) b =
      ∑ e : Fin Q, ∑ i : Fin (orderedRow member.fullDim.pathEnds
          (member.ident.row.symm e)).length,
        rowSlope member (chipSlope member root anchor) e i *
          (hit D small k hk e b (DegeneratePlacement.offsetVal
              (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) member hClosed
              e i) -
            hit D small k hk e b (DegeneratePlacement.offsetVal
              (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) member hClosed
              e (i.val + 1))) := by
  classical
  rw [pushDivisor_sub_eq]
  rw [sum_edges_eq_sum_rows member (fun edge ↦ edgeSlope member (chipSlope member root anchor) edge *
      ((if CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale
          (member.data.sourceEnds edge).1 = b then 1 else 0) -
        (if CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale
          (member.data.sourceEnds edge).2 = b then 1 else 0)))
    (fun edge hD ↦ by
      rw [realization_dangling D small hN hL k hk member hClosed hScale hD]
      ring)]
  refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← rowSlope_mul_sub member (chipSlope member root anchor) e i (fun v ↦
    if CorePencilCoverProducer.realization D small hN hL k hk member hClosed hScale v = b
      then 1 else 0)]
  unfold hit
  rw [realization_rowVertex D small hN hL k hk member hClosed hScale hCond e i
      (le_of_lt i.isLt),
    realization_rowVertex D small hN hL k hk member hClosed hScale hCond e (i.val + 1)
      i.isLt]

include hScale in
/-- **The big side of the identity**: the pushed Laplacian of the script, as a
sum over the unit steps of every big slot. -/
theorem pushDiv_prin_script (hCond : D.Conditions small.core)
    (b : (small.scale k hk).Vertex) :
    (ExpansionData.certificate D (small.scale k hk) hN hL).pushDiv
        (prin (D.bigSpec (small.scale k hk) hN hL).graph
          (script D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor))) b =
      ∑ e : Fin Q, ∑ o : Fin ((D.bigSpec (small.scale k hk) hN hL).length e),
        (slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) e (o.val + 1) -
          slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) e o.val) *
        (hit D small k hk e b o.val - hit D small k hk e b (o.val + 1)) := by
  classical
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  set B := D.bigSpec (small.scale k hk) hN hL
  have hSlope := B.isStepSlope_slotValueScript
    (compat D small hN hL k hk member hClosed hScale (chipSlope member root anchor) (chipPotential member hClosed root anchor) (chip_riseCompatible member hClosed root anchor))
  unfold GraphContractionCertificate.pushDiv
  simp only [script]
  rw [Finset.sum_congr rfl fun x _ ↦ by rw [B.prin_eq_sum_slopes hSlope x]]
  have hSwap : ∀ x : B.Vertex,
      (if (ExpansionData.certificate D (small.scale k hk) hN hL).vertexMap x = b then
        ∑ step : B.Step,
          ((if B.stepLeft step.1 step.2 = x then
              slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) step.1 (step.2.val + 1) -
                slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) step.1 step.2.val
            else 0) +
            (if B.stepRight step.1 step.2 = x then
              -(slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) step.1 (step.2.val + 1) -
                slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) step.1 step.2.val)
            else 0))
      else 0) =
        ∑ step : B.Step,
          ((if B.stepLeft step.1 step.2 = x then
              (if ExpansionData.vertexMap D (small.scale k hk) hN hL x = b then
                slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) step.1 (step.2.val + 1) -
                  slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) step.1 step.2.val
                else 0)
            else 0) +
            (if B.stepRight step.1 step.2 = x then
              (if ExpansionData.vertexMap D (small.scale k hk) hN hL x = b then
                -(slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) step.1
                    (step.2.val + 1) -
                  slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) step.1 step.2.val)
                else 0)
            else 0)) := by
    intro x
    by_cases hx : (ExpansionData.certificate D (small.scale k hk) hN hL).vertexMap x = b
    · rw [if_pos hx]
      refine Finset.sum_congr rfl fun step _ ↦ ?_
      have hx' : ExpansionData.vertexMap D (small.scale k hk) hN hL x = b := hx
      simp only [hx', if_true]
    · rw [if_neg hx]
      have hx' : ¬ ExpansionData.vertexMap D (small.scale k hk) hN hL x = b := hx
      simp only [hx', if_false, ite_self, add_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun x _ ↦ hSwap x, Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_add_distrib, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun o _ ↦ ?_
  rw [ExpansionData.vertexMap_stepLeft hCond' e o, ExpansionData.vertexMap_stepRight hCond' e o]
  unfold hit
  split_ifs <;> ring

include hScale in
/-- **The window computation, one slot at a time.**  The unit-step sum of the
script along the big slot `e` equals the sum over the member's occurrences of
the row slope times the difference of the indicator at the two ends of the
occurrence.  The script's step slope is the sum of the row slopes of the
occurrences covering that step, so each occurrence telescopes over its window
(`sum_window`); reversal maps windows to windows. -/
theorem slot_sum (e : Fin Q) (δ : ℕ → ℤ) :
    (∑ o : Fin ((D.bigSpec (small.scale k hk) hN hL).length e),
      (slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) e (o.val + 1) -
        slotValue D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) e o.val) *
      (δ o.val - δ (o.val + 1))) =
      ∑ i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length,
        rowSlope member (chipSlope member root anchor) e i *
          (δ (DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
              (degenerateLength D small) member hClosed e i) -
            δ (DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
              (degenerateLength D small) member hClosed e (i.val + 1))) := by
  have hFull := rowStart_full_le_length D small hN hL k hk member hClosed hScale e
  have hWin : ∀ i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length,
      rowStart member hClosed e i + rowLen member hClosed e i ≤
        (D.bigSpec (small.scale k hk) hN hL).length e :=
    fun i ↦ (rowStart_add_rowLen_le member hClosed e i).trans hFull
  simp only [offsetVal_eq]
  unfold slotValue slotPos
  cases hr : DegeneratePlacement.reverse member e
  · simp only [Bool.false_eq_true, if_false]
    have hDiff : ∀ o : ℕ,
        rowValue member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) e ((o + 1 : ℕ) : ℤ) -
            rowValue member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) e (o : ℤ) =
          ∑ i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length,
            rowSlope member (chipSlope member root anchor) e i *
              (if rowStart member hClosed e i ≤ o ∧
                  o < rowStart member hClosed e i + rowLen member hClosed e i
                then (1 : ℤ) else 0) := by
      intro o
      unfold rowValue
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← mul_sub, show ((o + 1 : ℕ) : ℤ) = (o : ℤ) + 1 by push_cast; ring,
        ramp_succ_sub _ _ _ (by positivity)]
      split_ifs <;> omega
    rw [Finset.sum_congr rfl fun o _ ↦ by rw [hDiff o.val]]
    rw [Fin.sum_univ_eq_sum_range (fun o ↦ (∑ i : Fin (orderedRow member.fullDim.pathEnds
        (member.ident.row.symm e)).length, rowSlope member (chipSlope member root anchor) e i *
          (if rowStart member hClosed e i ≤ o ∧
              o < rowStart member hClosed e i + rowLen member hClosed e i
            then (1 : ℤ) else 0)) * (δ o - δ (o + 1)))]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [mul_assoc]
    rw [← Finset.mul_sum, sum_window δ _ _ _ (hWin i)]
    show _ = rowSlope member (chipSlope member root anchor) e i *
      (δ (rowStart member hClosed e i) - δ (rowStart member hClosed e (i.val + 1)))
    rw [rowStart_succ]
  · simp only [if_true]
    have hDiff : ∀ o : ℕ, o < (D.bigSpec (small.scale k hk) hN hL).length e →
        rowValue member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) e
            (((D.bigSpec (small.scale k hk) hN hL).length e : ℤ) - ((o + 1 : ℕ) : ℤ)) -
          rowValue member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) e
            (((D.bigSpec (small.scale k hk) hN hL).length e : ℤ) - (o : ℤ)) =
          ∑ i : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length,
            rowSlope member (chipSlope member root anchor) e i *
              -(if (D.bigSpec (small.scale k hk) hN hL).length e -
                    rowStart member hClosed e i - rowLen member hClosed e i ≤ o ∧
                  o < (D.bigSpec (small.scale k hk) hN hL).length e - rowStart member hClosed e i
                then (1 : ℤ) else 0) := by
      intro o ho
      unfold rowValue
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hStep := ramp_succ_sub
        (((D.bigSpec (small.scale k hk) hN hL).length e : ℤ) - ((o + 1 : ℕ) : ℤ))
        (rowStart member hClosed e i) (rowLen member hClosed e i) (by positivity)
      rw [show ((D.bigSpec (small.scale k hk) hN hL).length e : ℤ) - ((o + 1 : ℕ) : ℤ) + 1 =
        ((D.bigSpec (small.scale k hk) hN hL).length e : ℤ) - (o : ℤ) by push_cast; ring]
        at hStep
      rw [← mul_sub, ← neg_sub, hStep]
      have := hWin i
      split_ifs <;> omega
    rw [Finset.sum_congr rfl fun o _ ↦ by rw [hDiff o.val o.isLt]]
    rw [Fin.sum_univ_eq_sum_range (fun o ↦ (∑ i : Fin (orderedRow member.fullDim.pathEnds
        (member.ident.row.symm e)).length, rowSlope member (chipSlope member root anchor) e i *
          -(if (D.bigSpec (small.scale k hk) hN hL).length e -
                rowStart member hClosed e i - rowLen member hClosed e i ≤ o ∧
              o < (D.bigSpec (small.scale k hk) hN hL).length e - rowStart member hClosed e i
            then (1 : ℤ) else 0)) * (δ o - δ (o + 1)))]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hW := hWin i
    have hEq : ∀ o ∈ Finset.range ((D.bigSpec (small.scale k hk) hN hL).length e),
        rowSlope member (chipSlope member root anchor) e i *
            -(if (D.bigSpec (small.scale k hk) hN hL).length e -
                  rowStart member hClosed e i - rowLen member hClosed e i ≤ o ∧
                o < (D.bigSpec (small.scale k hk) hN hL).length e - rowStart member hClosed e i
              then (1 : ℤ) else 0) * (δ o - δ (o + 1)) =
          -rowSlope member (chipSlope member root anchor) e i *
            ((if (D.bigSpec (small.scale k hk) hN hL).length e -
                  rowStart member hClosed e i - rowLen member hClosed e i ≤ o ∧
                o < (D.bigSpec (small.scale k hk) hN hL).length e -
                  rowStart member hClosed e i - rowLen member hClosed e i +
                    rowLen member hClosed e i
              then (1 : ℤ) else 0) * (δ o - δ (o + 1))) := by
      intro o _
      have hIff : (o < (D.bigSpec (small.scale k hk) hN hL).length e -
          rowStart member hClosed e i) ↔
          (o < (D.bigSpec (small.scale k hk) hN hL).length e -
            rowStart member hClosed e i - rowLen member hClosed e i +
              rowLen member hClosed e i) := by omega
      simp only [hIff]
      ring
    rw [Finset.sum_congr rfl hEq, ← Finset.mul_sum]
    have hSum' := sum_window δ ((D.bigSpec (small.scale k hk) hN hL).length e)
      ((D.bigSpec (small.scale k hk) hN hL).length e -
        rowStart member hClosed e i - rowLen member hClosed e i)
      (rowLen member hClosed e i) (by omega)
    rw [hSum']
    show _ = rowSlope member (chipSlope member root anchor) e i *
      (δ ((D.bigSpec (small.scale k hk) hN hL).length e - rowStart member hClosed e i) -
        δ ((D.bigSpec (small.scale k hk) hN hL).length e -
          rowStart member hClosed e (i.val + 1)))
    rw [rowStart_succ,
      show (D.bigSpec (small.scale k hk) hN hL).length e -
        rowStart member hClosed e i - rowLen member hClosed e i + rowLen member hClosed e i =
        (D.bigSpec (small.scale k hk) hN hL).length e - rowStart member hClosed e i by omega,
      show (D.bigSpec (small.scale k hk) hN hL).length e -
        (rowStart member hClosed e i + rowLen member hClosed e i) =
        (D.bigSpec (small.scale k hk) hN hL).length e -
          rowStart member hClosed e i - rowLen member hClosed e i by omega]
    ring

include hScale in
/-- **(T), proved.**  Any two pushed pencil members are linearly equivalent on the
small subdivision: their difference is the Laplacian of the descended script. -/
theorem linear_equiv_pushDivisor (hCond : D.Conditions small.core) :
    linear_equiv (small.scale k hk).graph
      (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root))
      (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale anchor)) := by
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  unfold linear_equiv
  rw [principal_iff_eq_prin]
  refine ⟨smallScript D small hN hL k hk member hClosed (chipSlope member root anchor) (chipPotential member hClosed root anchor) hCond, ?_⟩
  rw [← (ExpansionData.certificate D (small.scale k hk) hN hL).pushDiv_prin_pullScript
      (ExpansionData.certificate_valid hCond'),
    ← script_eq_pullScript D small hN hL k hk member hClosed hScale (chipSlope member root anchor) (chipPotential member hClosed root anchor) (chip_riseCompatible member hClosed root anchor) hCond]
  funext b
  rw [Pi.sub_apply, pushDivisor_sub_eq_rows D small hN hL k hk member hClosed hScale root
    anchor hCond b, pushDiv_prin_script D small hN hL k hk member hClosed hScale root anchor
    hCond b]
  exact Finset.sum_congr rfl fun e _ ↦
    (slot_sum D small hN hL k hk member hClosed hScale root anchor e (hit D small k hk e b)).symm

end Compare

/-! ## 8.  The main theorems -/

section Record

variable {n p N Q degree : ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)

/-- **(T), `PencilTransport`, at every root, for every closed member over every
expansion datum satisfying `ExpansionData.Conditions`.** -/
theorem pencilTransport (hCond : D.Conditions small.core) (root : member.target.V) :
    CorePencilCoverProducer.PencilTransport D small hN hL k hk member hClosed hScale root :=
  fun root' ↦ linear_equiv_pushDivisor D small hN hL k hk member hClosed hScale root root' hCond

include hScale in
/-- **`DoubleRowInterior` for loop doubles.**  If every `double` slot displays a
loop, the member's row over it has an interior vertex strictly inside the chain.

Proof: the row's two ends are branch vertices whose labels have the same
`D.fib` (the loop), so every integral potential on the target whose rises are
integral multiples of the realized lengths takes the same value at their images
(`corePotential_eq_of_fib_eq`: the fibre is connected through contracted slots,
along whose zero-length rows such a potential is constant).  If no interior row
vertex lay strictly inside the chain, one occurrence would carry the whole length
and every other occurrence would have length zero; the potential that rises only
along that occurrence's target edge then separates the two ends. -/
theorem doubleRowInterior_of_loopDoubles (hCond : D.Conditions small.core)
    (hLoop : CorePencilCoverProducer.LoopDoubles D small.core) :
    CorePencilCoverProducer.DoubleRowInterior D small hN hL k hk member hClosed := by
  classical
  intro e j₁ j₂ hk2
  have hne : D.kind e ≠ SlotKind.contracted := by
    rw [hk2]
    exact fun h ↦ by cases h
  have hFull : rowStart member hClosed e
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length =
      (D.bigSpec (small.scale k hk) hN hL).length e :=
    integralPrefix_full_of_ne D small hN hL k hk member hClosed hScale e hne
  have hLenB : (D.bigSpec (small.scale k hk) hN hL).length e =
      k * small.length j₁ + k * small.length j₂ := by
    show kindLength (small.scale k hk) (D.kind e) = _
    rw [hk2]
    rfl
  have hLenPos := (D.bigSpec (small.scale k hk) hN hL).length_pos e
  by_contra hNo
  -- every interior prefix is `0` or the full length
  have hInt : ∀ j, 0 < j →
      j < (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length →
      rowStart member hClosed e j = 0 ∨
        rowStart member hClosed e j = (D.bigSpec (small.scale k hk) hN hL).length e := by
    intro j hj0 hjl
    have hle : rowStart member hClosed e j ≤ (D.bigSpec (small.scale k hk) hN hL).length e :=
      (rowStart_le_full member hClosed e j).trans hFull.le
    by_contra hj
    apply hNo
    refine ⟨⟨member.ident.row.symm e, ⟨j - 1, by omega⟩⟩, Equiv.apply_symm_apply _ _, ?_, ?_⟩
    · show 0 < DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed e (j - 1 + 1)
      rw [show j - 1 + 1 = j by omega, offsetVal_eq]
      cases DegeneratePlacement.reverse member e <;> simp <;> omega
    · show DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed e (j - 1 + 1) < _
      rw [show j - 1 + 1 = j by omega, offsetVal_eq, ← hLenB]
      cases DegeneratePlacement.reverse member e <;> simp <;> omega
  -- the first prefix to leave `0` jumps to the full length
  have hEx : ∃ j, 1 ≤ rowStart member hClosed e j :=
    ⟨(orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length, by omega⟩
  have hJ : 1 ≤ rowStart member hClosed e (Nat.find hEx) := Nat.find_spec hEx
  have hJpos : 0 < Nat.find hEx := by
    by_contra h
    rw [show Nat.find hEx = 0 by omega, rowStart_zero] at hJ
    omega
  have hJle : Nat.find hEx ≤ (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length :=
    Nat.find_min' hEx (by omega)
  have hJm : rowStart member hClosed e (Nat.find hEx - 1) = 0 := by
    have := Nat.find_min hEx (show Nat.find hEx - 1 < Nat.find hEx by omega)
    omega
  have hJv : rowStart member hClosed e (Nat.find hEx) =
      (D.bigSpec (small.scale k hk) hN hL).length e := by
    rcases Nat.lt_or_ge (Nat.find hEx)
        (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length with h | h
    · rcases hInt _ hJpos h with h' | h' <;> omega
    · rw [show Nat.find hEx =
        (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length by omega, hFull]
  set i0 : Fin (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length :=
    ⟨Nat.find hEx - 1, by omega⟩ with hi0
  have hL0 : rowLen member hClosed e i0 = (D.bigSpec (small.scale k hk) hN hL).length e := by
    have h := rowStart_succ member hClosed e i0
    have h' : rowStart member hClosed e (Nat.find hEx - 1 + 1) =
        rowStart member hClosed e (Nat.find hEx - 1) + rowLen member hClosed e i0 := h
    rw [show Nat.find hEx - 1 + 1 = Nat.find hEx by omega] at h'
    omega
  have hOthers : ∀ i, i ≠ i0 → rowLen member hClosed e i = 0 := by
    intro i hi
    have hSum := sum_rowLen member hClosed e
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hL0, hFull] at hSum
    have hz : (∑ x ∈ Finset.univ.erase i0, (rowLen member hClosed e x : ℤ)) = 0 := by linarith
    have hnn : ∀ x ∈ Finset.univ.erase i0, (0 : ℤ) ≤ rowLen member hClosed e x :=
      fun _ _ ↦ by positivity
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz i
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    exact_mod_cast this
  -- the separating potential
  set t := ((orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i0]).1.1 with ht
  let s : member.target.edges → ℤ := fun t' ↦ if t' = t then 1 else 0
  let P : member.target.V → ℤ := TreeMetricPotential.integrate
    (fun t' ↦ s t' * ((memberRealization member hClosed).targetLength t' : ℤ))
  have hRise : RiseCompatible member hClosed s P := fun t' ↦
    TreeMetricPotential.integrate_rise member.fullDim.targetConnected member.fullDim.targetGenus _ t'
  have hFib : D.fib (D.bigCore.tail e) = D.fib (D.bigCore.head e) := by
    obtain ⟨h1, -, h3⟩ := (ExpansionData.compatible_of_conditions hCond e).2.2 j₁ j₂ hk2
    rw [h1, h3]
    exact hLoop e j₁ j₂ hk2
  have hCP := corePotential_eq_of_fib_eq D small hN hL k hk member hClosed hScale s P hRise hCond
    hFib
  have hC := compat D small hN hL k hk member hClosed hScale s P hRise
  have hEq : slotValue D small hN hL k hk member hClosed s P e 0 =
      slotValue D small hN hL k hk member hClosed s P e
        ((D.bigSpec (small.scale k hk) hN hL).length e) :=
    (hC.tail e).trans (hCP.trans (hC.head e).symm)
  have hPsi : sourcePotential member P
        (rowVertex member.fullDim (member.ident.row.symm e)
          (orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length) =
      sourcePotential member P (rowVertex member.fullDim (member.ident.row.symm e) 0) := by
    unfold slotValue slotPos at hEq
    cases hr : DegeneratePlacement.reverse member e
    · simp only [hr, Bool.false_eq_true, if_false, Nat.cast_zero] at hEq
      rw [rowValue_of_nonpos _ _ _ _ _ le_rfl,
        rowValue_of_ge _ _ _ _ hRise _ (by rw [hFull])] at hEq
      exact hEq.symm
    · simp only [hr, if_true, Nat.cast_zero, sub_zero, sub_self] at hEq
      rw [rowValue_of_ge _ _ _ _ hRise _ (by rw [hFull]),
        rowValue_of_nonpos _ _ _ _ _ le_rfl] at hEq
      exact hEq
  have hTel := sum_rowSlope_mul_rowLen member hClosed s P hRise e
  rw [hPsi, sub_self, Finset.sum_eq_single i0 (fun i _ hi ↦ by rw [hOthers i hi]; simp)
    (by simp), hL0] at hTel
  have hSlope : rowSlope member s e i0 ≠ 0 := by
    have hidx := GluingDatum.sourceEdgeIndex_pos member.data
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm e))[i0]
    have hs : s t = 1 := if_pos rfl
    unfold rowSlope edgeSlope
    rw [← ht, hs]
    split_ifs <;> omega
  rcases mul_eq_zero.mp hTel with h | h
  · exact hSlope h
  · exact absurd h (by exact_mod_cast hLenPos.ne')

include hScale in
/-- **`ForestContractionRank` for loop-double data**:
`CorePencilCoverProducer.forestContractionRank_of_transport_doubleRowInterior` with both
of its inputs discharged. -/
theorem forestContractionRank_of_loopDoubles (hCond : D.Conditions small.core)
    (hLoop : CorePencilCoverProducer.LoopDoubles D small.core)
    (hCoreConn : small.core.Connected) (root : member.target.V) :
    ForestContractionRank D small hN hL k hk member hClosed hScale root :=
  CorePencilCoverProducer.forestContractionRank_of_transport_doubleRowInterior D small hN hL k
    hk member hClosed hScale hCond hCoreConn root
    (pencilTransport D small hN hL k hk member hClosed hScale hCond root)
    (doubleRowInterior_of_loopDoubles D small hN hL k hk member hClosed hScale hCond hLoop)

end Record

/-! ## 9.  The supply -/

section Supply

/-- **`MarkerFreePencilCoverSupply`, proved.**  Through
`CorePencilCoverProducer.markerFreePencilCoverSupply_of_transport_doubleRowInterior`:
(T) is `pencilTransport` and the double rows are `doubleRowInterior_of_loopDoubles`.
Of the supply's premises only `D.Conditions small.core` and `LoopDoubles` are used. -/
theorem markerFreePencilCoverSupply : CorePencilCoverProducer.MarkerFreePencilCoverSupply :=
  CorePencilCoverProducer.markerFreePencilCoverSupply_of_transport_doubleRowInterior
    fun small D hN hL hCond hLoop _ _ _ _ k hk member hClosed hScale _ ↦
      ⟨⟨Classical.choice member.target.instNonempty,
          pencilTransport D small hN hL k hk member hClosed hScale hCond _⟩,
        doubleRowInterior_of_loopDoubles D small hN hL k hk member hClosed hScale hCond hLoop⟩

end Supply

end DraismaVargas.Count.PencilTransportProducer
