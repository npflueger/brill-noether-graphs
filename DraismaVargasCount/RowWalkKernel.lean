module

public import DraismaVargasCount.TreeMetricPotential
public import DraismaVargas.Infrastructure.NonnegativeRationalRealization
public import DraismaVargas.LocalCases.W4StableSource
public import DraismaVargas.LocalCases.StableLocalProperties

@[expose] public section

/-!
# Rise-compatible potentials along the rows of a gluing datum

Fix a gluing datum `data` over a target tree and a closed-cone integral realization `R` of it
(zero lengths allowed). A target potential `P` is **rise-compatible** with integral slopes `s`
(`RiseCompatible`) if it rises along every target edge by the slope times the realized length.
Pulled back to the source (`sourcePotential`) it rises along a source edge by `edgeSlope` times
the realized source length (`sourcePotential_rise`), and the fibre difference of the tree slope
with incidence `anchor − root` is its signed incidence (`fibre_sub_eq`, `sum_fibre_sub`).

A **row** is a list of source occurrences walked through the vertices `vtx 0, vtx 1, …`
(`IsWalk`: occurrence `i` is incident to `vtx i` and is left by its other end). Along it the
prefix lengths `start`, the lengths `len` and the slopes `slope` read in the walk direction
satisfy the telescoping identities of `RowAlgebra`: the potential rises along each occurrence by
the slope times the length (`slope_mul_len`, `sum_slope_mul_len`). If every rise-compatible
potential agrees at the two ends of a row, no single occurrence can carry a positive length with
all others of length zero (`not_single_long`): the potential rising only along that occurrence's
target edge separates the ends.

Nothing here refers to a member, a frame, a slot or a core: the fibre members of
`PencilTransportProducer`, the typed frames of `DiagonalSecant` and the tripod rows of
`GenusSixExistence` supply `data`, `R`, the rows and the walk hypotheses.

## What is proved

§1 `RiseCompatible`, `sourcePotential`, `edgeSlope`, `fibreWeight`, `sourcePotential_rise`,
`fibre_sub_eq`, `sum_fibre_sub`; §2 the row data `start`, `len`, `slope`, `IsWalk`, and
`start_succ`, `start_zero`, `slope_mul_sub`, `slope_mul_len`, `sum_slope_mul_len`,
**`not_single_long`**; §3 **`sum_edges_eq_sum_rows`**, the sum over the surviving edges as a sum
over the rows of any partition of them.
-/

namespace DraismaVargas.Count.RowWalkKernel

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)

/-! ## 1.  Rise-compatible potentials, pulled back to the source -/

section Datum

/-- A target potential `P` with integral slopes `s` rising along every target edge by the slope
times the realized length of that edge.  Zero lengths are allowed, and then the rise is zero. -/
def RiseCompatible {data : GluingDatum target degree} (R : data.NonnegativeIntegralRealization)
    (s : target.edges → ℤ) (P : target.V → ℤ) : Prop :=
  ∀ t : target.edges,
    P (t : target.V × target.V).2 - P (t : target.V × target.V).1 =
      s t * (R.targetLength t : ℤ)

/-- The pulled-back potential on the source. -/
def sourcePotential (P : target.V → ℤ) (x : data.SourceVertex) : ℤ := P x.1.1

/-- The slope of the pulled-back potential along one source edge, per unit of its realized
length. -/
def edgeSlope (s : target.edges → ℤ) (edge : data.SourceEdge) : ℤ :=
  s edge.1.1 * (data.sourceEdgeIndex edge : ℤ)

/-- The weight of a source vertex in the pull-back fibre over the target vertex `root`. -/
def fibreWeight (root : target.V) (raw : data.SourceVertex) : ℤ :=
  if raw.1.1 = root then ((data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0

/-- Along a source edge the pulled-back potential rises by the edge slope times the realized
source length: the dilation equation. -/
theorem sourcePotential_rise {data : GluingDatum target degree}
    {R : data.NonnegativeIntegralRealization} {s : target.edges → ℤ} {P : target.V → ℤ}
    (hRise : RiseCompatible R s P) (edge : data.SourceEdge) :
    sourcePotential data P (data.sourceEnds edge).2 -
        sourcePotential data P (data.sourceEnds edge).1 =
      edgeSlope data s edge * (R.sourceLength edge : ℤ) := by
  have h := hRise edge.1.1
  have hDilZ : ((data.sourceEdgeIndex edge : ℕ) : ℤ) * (R.sourceLength edge : ℤ) =
      (R.targetLength edge.1.1 : ℤ) := by
    exact_mod_cast R.dilation_length edge
  unfold sourcePotential edgeSlope
  change P (edge.1.1 : target.V × target.V).2 - P (edge.1.1 : target.V × target.V).1 = _
  rw [h, ← hDilZ]
  ring

variable (hConn : graph_connected target) (hGenus : genus target = 0)

/-- **The fibre difference is the pulled-back incidence**: the sheet-partition refinement
equation `sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence` against the tree slope with
incidence `anchor − root`. -/
theorem fibre_sub_eq (root anchor : target.V) (raw : data.SourceVertex) :
    fibreWeight data anchor raw - fibreWeight data root raw =
      ∑ edge : data.SourceEdge,
        ((if (data.sourceEnds edge).1 = raw then
            edgeSlope data (TreeMetricPotential.chipSlope data hConn hGenus root anchor) edge
          else 0) -
          (if (data.sourceEnds edge).2 = raw then
            edgeSlope data (TreeMetricPotential.chipSlope data hConn hGenus root anchor) edge
          else 0)) := by
  have h := data.sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence
    (TreeMetricPotential.chipSlope data hConn hGenus root anchor) raw
  have hInc := TreeMetricPotential.chipSlope_incidence data hConn hGenus root anchor raw.1.1
  unfold sourceEdgeIncidence at h
  rw [hInc] at h
  have hL : ∑ edge : data.SourceEdge,
      ((if (data.sourceEnds edge).1 = raw then
          edgeSlope data (TreeMetricPotential.chipSlope data hConn hGenus root anchor) edge
        else 0) -
        (if (data.sourceEnds edge).2 = raw then
          edgeSlope data (TreeMetricPotential.chipSlope data hConn hGenus root anchor) edge
        else 0)) =
      ∑ edge : data.SourceEdge,
        ((if (data.sourceEnds edge).1 = raw then
            (data.sourceEdgeIndex edge : ℤ) *
              TreeMetricPotential.chipSlope data hConn hGenus root anchor edge.1.1 else 0) +
          (if (data.sourceEnds edge).2 = raw then
            (data.sourceEdgeIndex edge : ℤ) *
              -TreeMetricPotential.chipSlope data hConn hGenus root anchor edge.1.1 else 0)) := by
    refine Finset.sum_congr rfl fun edge _ ↦ ?_
    unfold edgeSlope
    split_ifs <;> ring
  rw [hL, h]
  unfold fibreWeight
  split_ifs <;> ring

/-- **The pushed fibre difference, edge by edge.**  Along any map `ρ` out of the source, the
pushforward of `fibreWeight anchor - fibreWeight root` at `b` is the sum over source edges of the
edge slope times the difference of the two end indicators. -/
theorem sum_fibre_sub (root anchor : target.V) {X : Type*} [DecidableEq X]
    (ρ : data.SourceVertex → X) (b : X) :
    (∑ raw : data.SourceVertex,
      if ρ raw = b then fibreWeight data anchor raw - fibreWeight data root raw else 0) =
      ∑ edge : data.SourceEdge,
        edgeSlope data (TreeMetricPotential.chipSlope data hConn hGenus root anchor) edge *
          ((if ρ (data.sourceEnds edge).1 = b then 1 else 0) -
            (if ρ (data.sourceEnds edge).2 = b then 1 else 0)) := by
  classical
  set σ := edgeSlope data (TreeMetricPotential.chipSlope data hConn hGenus root anchor)
  have hStep : ∀ raw : data.SourceVertex,
      (if ρ raw = b then fibreWeight data anchor raw - fibreWeight data root raw else 0) =
        ∑ edge : data.SourceEdge,
          (if ρ raw = b then
            ((if (data.sourceEnds edge).1 = raw then σ edge else 0) -
              (if (data.sourceEnds edge).2 = raw then σ edge else 0)) else 0) := by
    intro raw
    by_cases hb : ρ raw = b
    · simp only [ite_eq_left hb]
      exact fibre_sub_eq data hConn hGenus root anchor raw
    · simp only [ite_eq_right hb, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun raw _ ↦ hStep raw, Finset.sum_comm]
  refine Finset.sum_congr rfl fun edge _ ↦ ?_
  have hSplit : ∀ raw : data.SourceVertex,
      (if ρ raw = b then
        ((if (data.sourceEnds edge).1 = raw then σ edge else 0) -
          (if (data.sourceEnds edge).2 = raw then σ edge else 0)) else 0) =
        (if (data.sourceEnds edge).1 = raw then (if ρ raw = b then σ edge else 0) else 0) -
        (if (data.sourceEnds edge).2 = raw then (if ρ raw = b then σ edge else 0) else 0) := by
    intro raw
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun raw _ ↦ hSplit raw, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  split_ifs <;> ring

end Datum

/-! ## 2.  One row -/

section Row

variable {data} (R : data.NonnegativeIntegralRealization) (row : List data.SourceEdge)
  (vtx : ℕ → data.SourceVertex)

/-- The integral offset, from the row's start, of the `j`-th row vertex. -/
def start (j : ℕ) : ℕ := ((row.take j).map R.sourceLength).sum

/-- The realized integral length of the `i`-th occurrence. -/
def len (i : Fin row.length) : ℕ := R.sourceLength row[i]

/-- The slope of the pulled-back potential along the `i`-th occurrence, read in the walk
direction. -/
def slope (s : target.edges → ℤ) (i : Fin row.length) : ℤ :=
  if (data.sourceEnds row[i]).1 = vtx i then edgeSlope data s row[i] else -edgeSlope data s row[i]

/-- `vtx` walks along `row`: occurrence `i` is incident to `vtx i` and is left by its other end. -/
abbrev IsWalk : Prop :=
  ∀ i (h : i < row.length),
    Incident data row[i] (vtx i) ∧ vtx (i + 1) = otherEnd data row[i] (vtx i)

theorem start_succ (i : Fin row.length) :
    start R row (i.val + 1) = start R row i + len R row i := by
  unfold start len
  rw [List.take_add_one, List.getElem?_eq_getElem i.isLt]
  simp

theorem start_zero : start R row 0 = 0 := by simp [start]

variable {row vtx} (hW : IsWalk row vtx)
include hW

/-- `slope` reads the edge slope in the walk order: for any function `f` on source vertices, the
signed differences agree. -/
theorem slope_mul_sub (s : target.edges → ℤ) (i : Fin row.length) (f : data.SourceVertex → ℤ) :
    slope row vtx s i * (f (vtx i) - f (vtx (i.val + 1))) =
      edgeSlope data s row[i] * (f (data.sourceEnds row[i]).1 - f (data.sourceEnds row[i]).2) := by
  have hInc : Incident data row[i] (vtx i) := (hW i i.isLt).1
  have hSucc : vtx (i.val + 1) = otherEnd data row[i] (vtx i) := (hW i i.isLt).2
  unfold slope
  rw [hSucc]
  unfold otherEnd
  by_cases h : (data.sourceEnds row[i]).1 = vtx i
  · rw [ite_eq_left h, ite_eq_left h, h]
  · rw [ite_eq_right h, ite_eq_right h, hInc.resolve_left h]
    ring

/-- Along one occurrence the pulled-back potential rises by the slope times the length. -/
theorem slope_mul_len {s : target.edges → ℤ} {P : target.V → ℤ} (hRise : RiseCompatible R s P)
    (i : Fin row.length) :
    slope row vtx s i * (len R row i : ℤ) =
      sourcePotential data P (vtx (i.val + 1)) - sourcePotential data P (vtx i) := by
  have hInc : Incident data row[i] (vtx i) := (hW i i.isLt).1
  have hSucc : vtx (i.val + 1) = otherEnd data row[i] (vtx i) := (hW i i.isLt).2
  have hRise := sourcePotential_rise hRise row[i]
  unfold slope len
  rw [hSucc]
  unfold otherEnd
  by_cases h : (data.sourceEnds row[i]).1 = vtx i
  · rw [ite_eq_left h, ite_eq_left h, ← h, hRise]
  · rw [ite_eq_right h, ite_eq_right h, ← hInc.resolve_left h]
    linarith

/-- The pulled-back potential telescopes along the whole row. -/
theorem sum_slope_mul_len {s : target.edges → ℤ} {P : target.V → ℤ}
    (hRise : RiseCompatible R s P) :
    (∑ i : Fin row.length, slope row vtx s i * (len R row i : ℤ)) =
      sourcePotential data P (vtx row.length) - sourcePotential data P (vtx 0) := by
  rw [Finset.sum_congr rfl fun i _ ↦ slope_mul_len R hW hRise i]
  exact Finset.sum_range_sub (fun j ↦ sourcePotential data P (vtx j)) _ ▸
    (Fin.sum_univ_eq_sum_range (fun j ↦ sourcePotential data P (vtx (j + 1)) -
      sourcePotential data P (vtx j)) _)

/-- **The separating potential.**  If every rise-compatible potential takes the same value at
the two ends of the row, the row cannot have exactly one occurrence of positive length: the
potential rising only along that occurrence's target edge (`TreeMetricPotential.integrate`)
would differ at the two ends. -/
theorem not_single_long (hConn : graph_connected target) (hGenus : genus target = 0)
    (i0 : Fin row.length) (hOthers : ∀ i, i ≠ i0 → len R row i = 0) (hPos : 0 < len R row i0)
    (hEnds : ∀ s P, RiseCompatible R s P →
      sourcePotential data P (vtx row.length) = sourcePotential data P (vtx 0)) : False := by
  classical
  set t := (row[i0]).1.1 with ht
  let s : target.edges → ℤ := fun t' ↦ if t' = t then 1 else 0
  let P : target.V → ℤ :=
    TreeMetricPotential.integrate (fun t' ↦ s t' * (R.targetLength t' : ℤ))
  have hRise : RiseCompatible R s P := fun t' ↦
    TreeMetricPotential.integrate_rise hConn hGenus _ t'
  have hTel := sum_slope_mul_len R hW hRise
  rw [hEnds s P hRise, sub_self, Finset.sum_eq_single i0 (fun i _ hi ↦ by rw [hOthers i hi]; simp)
    (by simp)] at hTel
  have hSlope : slope row vtx s i0 ≠ 0 := by
    have hidx := GluingDatum.sourceEdgeIndex_pos data row[i0]
    have hs : s t = 1 := ite_eq_left rfl
    unfold slope edgeSlope
    rw [← ht, hs]
    split_ifs <;> omega
  rcases mul_eq_zero.mp hTel with h | h
  · exact hSlope h
  · exact absurd h (by exact_mod_cast hPos.ne')

end Row

/-! ## 3.  The rows of a partition of the surviving edges -/

/-- **The row decomposition.**  If the surviving edges are partitioned among rows without
repetition (`hNodup`, `hOne`), a function on source edges vanishing on the dangling ones sums to
the sum, over the rows, of its values along them. -/
theorem sum_edges_eq_sum_rows {Q : ℕ} (rows : Fin Q → List data.SourceEdge)
    (hNodup : ∀ e, (rows e).Nodup)
    (hOne : ∀ edge, ¬ IsDangling data edge → ∃! e, edge ∈ rows e)
    (g : data.SourceEdge → ℤ) (hDangling : ∀ edge, IsDangling data edge → g edge = 0) :
    (∑ edge : data.SourceEdge, g edge) =
      ∑ e : Fin Q, ∑ i : Fin (rows e).length, g (rows e)[i] := by
  classical
  have hStep : ∀ edge, g edge = ∑ e : Fin Q, if edge ∈ rows e then g edge else 0 := by
    intro edge
    by_cases hD : IsDangling data edge
    · simp [hDangling edge hD]
    · obtain ⟨e0, he0, huniq⟩ := hOne edge hD
      rw [Finset.sum_eq_single e0 (fun e _ hne ↦ ite_eq_right fun h ↦ hne (huniq e h)) (by simp),
        ite_eq_left he0]
  rw [Finset.sum_congr rfl fun edge _ ↦ hStep edge, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [← Finset.sum_filter,
    show Finset.univ.filter (· ∈ rows e) = (rows e).toFinset by ext; simp,
    List.sum_toFinset _ (hNodup e)]
  exact (Fin.sum_univ_fun_getElem _ g).symm

end DraismaVargas.Count.RowWalkKernel
