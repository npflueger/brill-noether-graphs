module

public import DraismaVargas.LocalCases.PresentationDecomposition

@[expose] public section

/-!
# A finite universal atlas of nonsingular length matrices

The finite march of `FiniteAtlasMarch` (`FiniteAtlasMarch.State.exists_terminal_reachable`)
needs three things about its chart type: that it is a `Fintype`, that it
carries a map `matrix : chart → Matrix coordinate coordinate ℚ`, and that every
displayed matrix is nonsingular.  Nothing in the
finite march inspects a chart label further -- the semantic candidate travels
separately, in `SemanticAtlasMarch.State.carriesPencil`.

So the chart need not be a classification of gluing data.  This module builds
the crude universal atlas instead: **every** rational matrix whose entries have
denominator dividing `degree !` and numerator at most
`degree ! * (Fintype.card coordinate * degree)`.  That finite set of matrices
contains the length matrix of every honest stable presentation of every degree
`degree` gluing datum over every target with `Fintype.card coordinate` edge
occurrences, and it contains a great many matrices that arise from no cover at
all.  The second fact is harmless; only finiteness is used.

## The bound

`GluingDatum.LengthMatrixPresentation.coefficient` is `1 / sourceEdgeIndex e`
on the target column containing `e` and `0` elsewhere, so the `(row, column)`
entry of the length matrix is

```
∑_{e ∈ presentation.path row, φ(e) = column} 1 / m(e).
```

Three crude estimates finish it.

* `sourceEdgeIndex_le_degree`: `m(e)` is the cardinality of a block of a
  `SheetPartition degree`, hence lies in `[1, degree]`, hence divides
  `degree !`.  So each term of the sum is `k / degree !` with `k ≤ degree !`.
* A duplicate-free row has at most `Fintype.card data.SourceEdge` entries, and
  `data.SourceEdge` embeds in `target.edges × Fin degree`, whose cardinality is
  `Fintype.card coordinate * degree` because `presentation.targetEdge` is an
  equivalence.
* Adding at most that many terms, each with numerator at most `degree !`, keeps
  the denominator and multiplies the numerator bound.

The duplicate-freeness input is `PresentationDecomposition.Decomposes.nodup`,
which is why the entry bound is stated for honest presentations.

## What is exported

* `sourceEdgeIndex_le_degree`, the index bound;
* `IsAtlasEntry` and `IsAtlasMatrix`, the finite entry set as a predicate, with
  `matrix_isAtlasMatrix_of_nodup` and the `Decomposes` corollary;
* `chart`, `atlasMatrix`, `atlasMatrix_det_ne_zero`;
* `encode` and `atlasMatrix_encode`, the registration direction that
  `FiniteAtlasMarch.State.exists_step_of_classified_first_wall` consumes as
  `houtgoingMatrix`.
-/

namespace DraismaVargas.LocalCases.MatrixAtlas

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.PresentationDecomposition

/-! ## 1.  The index bound -/

section IndexBound

variable {d : ℕ}

/-- A block of a partition of `Fin d` has at most `d` elements. -/
theorem blockCard_le_degree (partition : SheetPartition d) (i : Fin d) :
    partition.blockCard i ≤ d := by
  have hle : (partition.block i).card ≤ Fintype.card (Fin d) :=
    Finset.card_le_univ _
  simpa [SheetPartition.blockCard] using hle

end IndexBound

variable {target : CFGraph} {degree : ℕ}

/-- Every dilation index of a degree-`degree` gluing datum is at most
`degree`: it is the cardinality of a block of a `SheetPartition degree`. -/
theorem sourceEdgeIndex_le_degree (data : GluingDatum target degree)
    (e : data.SourceEdge) : data.sourceEdgeIndex e ≤ degree :=
  blockCard_le_degree _ _

/-! ## 2.  The entry bound -/

/-- The common denominator used by the atlas.  Any multiple of every index
`1, …, degree` would do; `degree !` is the cheapest to justify. -/
def denominator (degree : ℕ) : ℕ := Nat.factorial degree

theorem denominator_pos (degree : ℕ) : 0 < denominator degree :=
  Nat.factorial_pos degree

theorem denominator_ne_zero (degree : ℕ) : (denominator degree : ℚ) ≠ 0 := by
  exact_mod_cast (denominator_pos degree).ne'

/-- Every dilation index divides the atlas denominator. -/
theorem sourceEdgeIndex_dvd_denominator (data : GluingDatum target degree)
    (e : data.SourceEdge) : data.sourceEdgeIndex e ∣ denominator degree :=
  Nat.dvd_factorial (data.sourceEdgeIndex_pos e) (sourceEdgeIndex_le_degree data e)

/-- `IsScaled degree n q` says that `q = k / degree !` for a natural numerator
`k ≤ n`.  This is the finite set of allowed rationals, stated as a predicate so
that downstream users never have to build the `Finset`. -/
def IsScaled (degree n : ℕ) (q : ℚ) : Prop :=
  ∃ k : ℕ, k ≤ n ∧ q = (k : ℚ) / (denominator degree : ℚ)

theorem IsScaled.mono {degree m n : ℕ} {q : ℚ} (h : IsScaled degree m q)
    (hmn : m ≤ n) : IsScaled degree n q := by
  obtain ⟨k, hk, hq⟩ := h
  exact ⟨k, hk.trans hmn, hq⟩

theorem isScaled_zero (degree n : ℕ) : IsScaled degree n 0 :=
  ⟨0, Nat.zero_le _, by simp⟩

/-- One over an index is an allowed rational with numerator at most the
denominator. -/
theorem isScaled_one_div_sourceEdgeIndex (data : GluingDatum target degree)
    (e : data.SourceEdge) :
    IsScaled degree (denominator degree)
      (1 / (data.sourceEdgeIndex e : ℚ)) := by
  obtain ⟨k, hk⟩ := sourceEdgeIndex_dvd_denominator data e
  have hindex : (0 : ℚ) < (data.sourceEdgeIndex e : ℚ) := by
    exact_mod_cast data.sourceEdgeIndex_pos e
  refine ⟨k, ?_, ?_⟩
  · have hpos : 0 < data.sourceEdgeIndex e := data.sourceEdgeIndex_pos e
    calc k ≤ data.sourceEdgeIndex e * k := Nat.le_mul_of_pos_left _ hpos
      _ = denominator degree := hk.symm
  · have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hzero | hpos
      · rw [hzero, Nat.mul_zero] at hk
        exact absurd hk (denominator_pos degree).ne'
      · exact hpos
    have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hkpos.ne'
    have hcast : (denominator degree : ℚ) = (data.sourceEdgeIndex e : ℚ) * (k : ℚ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hk
    rw [hcast]
    rw [div_eq_div_iff hindex.ne' (mul_ne_zero hindex.ne' hkQ)]
    ring

/-- A finite sum of allowed rationals, each with numerator at most the
denominator, is allowed with the numerator bound multiplied by the length. -/
theorem isScaled_list_sum {α : Type*} (f : α → ℚ) :
    ∀ l : List α, (∀ a ∈ l, IsScaled degree (denominator degree) (f a)) →
      IsScaled degree (denominator degree * l.length) ((l.map f).sum) := by
  intro l
  induction l with
  | nil => intro _; simpa using isScaled_zero degree 0
  | cons a rest ih =>
      intro hmem
      obtain ⟨ka, hka, hfa⟩ := hmem a (by simp)
      obtain ⟨kr, hkr, hfr⟩ :=
        ih fun b hb => hmem b (List.mem_cons_of_mem _ hb)
      refine ⟨ka + kr, ?_, ?_⟩
      · have : denominator degree * (rest.length + 1)
            = denominator degree * rest.length + denominator degree := by ring
        simp only [List.length_cons, this]
        omega
      · rw [List.map_cons, List.sum_cons, hfa, hfr, ← add_div]
        push_cast
        ring

/-- A source-edge occurrence is determined by the target occurrence and the
sheet below it, so there are at most `Fintype.card target.edges * degree` of
them. -/
theorem card_sourceEdge_le (data : GluingDatum target degree) :
    Fintype.card data.SourceEdge ≤ Fintype.card target.edges * degree := by
  have hinj : Function.Injective
      (fun e : data.SourceEdge => (e.1 : target.edges × Fin degree)) :=
    fun a b hab => Subtype.ext hab
  have h := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_prod] using h

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The numerator bound of the atlas: the common denominator times the crude
count of source-edge occurrences available to a single row. -/
def numeratorBound (coordinate : Type*) [Fintype coordinate] (degree : ℕ) : ℕ :=
  denominator degree * (Fintype.card coordinate * degree)

/-- The finite set of rationals allowed as an atlas matrix entry: those of the
form `k / degree !` with `k : ℕ` and `k ≤ numeratorBound coordinate degree`. -/
def IsAtlasEntry (coordinate : Type*) [Fintype coordinate] (degree : ℕ)
    (q : ℚ) : Prop :=
  IsScaled degree (numeratorBound coordinate degree) q

/-- A matrix all of whose entries are allowed. -/
def IsAtlasMatrix (degree : ℕ) (m : Matrix coordinate coordinate ℚ) : Prop :=
  ∀ i j, IsAtlasEntry coordinate degree (m i j)

omit [Fintype coordinate] in
/-- Each matrix coefficient of a source occurrence is `k / degree !` with
`k ≤ degree !`. -/
theorem isScaled_coefficient {data : GluingDatum target degree}
    (presentation : data.LengthMatrixPresentation coordinate)
    (e : data.SourceEdge) (column : coordinate) :
    IsScaled degree (denominator degree)
      (GluingDatum.LengthMatrixPresentation.coefficient presentation e column) := by
  by_cases hTarget : presentation.targetEdge column = e.1.1
  · have hone :=
      GluingDatum.LengthMatrixPresentation.coefficient_mul_eq_cofactor_div
        presentation e column 1 hTarget
    rw [mul_one] at hone
    rw [hone]
    exact isScaled_one_div_sourceEdgeIndex data e
  · rw [GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
      presentation e column hTarget]
    exact isScaled_zero degree _

/-- **The entry bound.**  Every entry of the length matrix of a presentation
with duplicate-free rows is `k / degree !` with
`k ≤ degree ! * (Fintype.card coordinate * degree)`. -/
theorem matrix_isAtlasMatrix_of_nodup {data : GluingDatum target degree}
    (presentation : data.LengthMatrixPresentation coordinate)
    (hnodup : ∀ row, (presentation.path row).Nodup) :
    IsAtlasMatrix degree
      (GluingDatum.LengthMatrixPresentation.matrix presentation) := by
  intro row column
  have hsum :
      GluingDatum.LengthMatrixPresentation.matrix presentation row column =
        ((presentation.path row).map fun e =>
          GluingDatum.LengthMatrixPresentation.coefficient presentation e column).sum :=
    rfl
  have hscaled :
      IsScaled degree (denominator degree * (presentation.path row).length)
        (((presentation.path row).map fun e =>
          GluingDatum.LengthMatrixPresentation.coefficient presentation e column).sum) :=
    isScaled_list_sum _ _ fun e _ => isScaled_coefficient presentation e column
  have hlen : (presentation.path row).length ≤ Fintype.card coordinate * degree := by
    have h1 : (presentation.path row).length ≤ Fintype.card data.SourceEdge :=
      (hnodup row).length_le_card
    have h2 : Fintype.card data.SourceEdge ≤ Fintype.card target.edges * degree :=
      card_sourceEdge_le data
    have h3 : Fintype.card target.edges = Fintype.card coordinate :=
      (Fintype.card_congr presentation.targetEdge).symm
    rw [h3] at h2
    exact h1.trans h2
  refine (hsum ▸ hscaled).mono ?_
  exact Nat.mul_le_mul_left _ hlen

/-- The entry bound for an honest presentation, whose rows decompose the
pruned source and are therefore duplicate-free. -/
theorem matrix_isAtlasMatrix_of_decomposes {data : GluingDatum target degree}
    {presentation : data.LengthMatrixPresentation coordinate}
    (hdec : Decomposes presentation) :
    IsAtlasMatrix degree
      (GluingDatum.LengthMatrixPresentation.matrix presentation) :=
  matrix_isAtlasMatrix_of_nodup presentation hdec.nodup

/-- The allowed entries as a literal `Finset ℚ`:

```
atlasEntries coordinate degree =
  (Finset.range (degree ! * (Fintype.card coordinate * degree) + 1)).image
    fun k => (k : ℚ) / (degree ! : ℚ)
```
-/
def atlasEntries (coordinate : Type*) [Fintype coordinate] (degree : ℕ) :
    Finset ℚ :=
  (Finset.range (numeratorBound coordinate degree + 1)).image
    fun k : ℕ => (k : ℚ) / (denominator degree : ℚ)

omit [DecidableEq coordinate] in
theorem isAtlasEntry_iff_mem_atlasEntries (q : ℚ) :
    IsAtlasEntry coordinate degree q ↔ q ∈ atlasEntries coordinate degree := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩
  · intro hmem
    obtain ⟨k, hk, hq⟩ := Finset.mem_image.mp hmem
    exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hq.symm⟩

/-- The entry bound in `Finset` form. -/
theorem matrix_mem_atlasEntries {data : GluingDatum target degree}
    (presentation : data.LengthMatrixPresentation coordinate)
    (hnodup : ∀ row, (presentation.path row).Nodup) (row column : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix presentation row column ∈
      atlasEntries coordinate degree :=
  (isAtlasEntry_iff_mem_atlasEntries _).mp
    (matrix_isAtlasMatrix_of_nodup presentation hnodup row column)

/-! ## 3.  The atlas -/

/-- Decoding a matrix of numerators.  Entries are encoded by naturals bounded
by `numeratorBound coordinate degree` so that the matrices form a `Fintype`;
`ℚ` itself has none. -/
def decodeMatrix
    (a : coordinate → coordinate → Fin (numeratorBound coordinate degree + 1)) :
    Matrix coordinate coordinate ℚ :=
  fun i j => ((a i j : ℕ) : ℚ) / (denominator degree : ℚ)

omit [DecidableEq coordinate] in
theorem decodeMatrix_isAtlasMatrix
    (a : coordinate → coordinate → Fin (numeratorBound coordinate degree + 1)) :
    IsAtlasMatrix degree (decodeMatrix a) :=
  fun i j => ⟨(a i j : ℕ), Nat.lt_succ_iff.mp (a i j).isLt, rfl⟩

/-- **The chart type.**  A label is an allowed matrix of numerators together
with the proof that the rational matrix it decodes to is nonsingular. -/
def chart (coordinate : Type*) [Fintype coordinate] [DecidableEq coordinate]
    (degree : ℕ) : Type _ :=
  { a : coordinate → coordinate → Fin (numeratorBound coordinate degree + 1) //
    (decodeMatrix a).det ≠ 0 }

instance : DecidableEq (chart coordinate degree) := by
  unfold chart
  infer_instance

instance : Fintype (chart coordinate degree) := by
  unfold chart
  infer_instance

/-- The matrix displayed by a chart label. -/
def atlasMatrix (label : chart coordinate degree) :
    Matrix coordinate coordinate ℚ :=
  decodeMatrix label.1

/-- The nonsingularity hypothesis `hdet` of the finite march
(`FiniteAtlasMarch.State.exists_terminal_reachable`) is a projection. -/
theorem atlasMatrix_det_ne_zero (label : chart coordinate degree) :
    (atlasMatrix label).det ≠ 0 := label.2

theorem atlasMatrix_isAtlasMatrix (label : chart coordinate degree) :
    IsAtlasMatrix degree (atlasMatrix label) :=
  decodeMatrix_isAtlasMatrix label.1

/-! ## 4.  Registration -/

/-- The numerator of an allowed entry. -/
noncomputable def encodeEntry {q : ℚ} (h : IsAtlasEntry coordinate degree q) :
    Fin (numeratorBound coordinate degree + 1) :=
  ⟨Classical.choose h, Nat.lt_succ_of_le (Classical.choose_spec h).1⟩

omit [DecidableEq coordinate] in
theorem decode_encodeEntry {q : ℚ} (h : IsAtlasEntry coordinate degree q) :
    ((encodeEntry h : ℕ) : ℚ) / (denominator degree : ℚ) = q :=
  (Classical.choose_spec h).2.symm

/-- The numerator matrix of an allowed matrix. -/
noncomputable def encodeMatrix (m : Matrix coordinate coordinate ℚ)
    (h : IsAtlasMatrix degree m) :
    coordinate → coordinate → Fin (numeratorBound coordinate degree + 1) :=
  fun i j => encodeEntry (h i j)

omit [DecidableEq coordinate] in
@[simp] theorem decodeMatrix_encodeMatrix (m : Matrix coordinate coordinate ℚ)
    (h : IsAtlasMatrix degree m) : decodeMatrix (encodeMatrix m h) = m := by
  funext i j
  exact decode_encodeEntry (h i j)

/-- **Registration.**  An allowed nonsingular matrix is displayed by a chart
label. -/
noncomputable def encode (m : Matrix coordinate coordinate ℚ)
    (h : IsAtlasMatrix degree m) (hdet : m.det ≠ 0) : chart coordinate degree :=
  ⟨encodeMatrix m h, by rw [decodeMatrix_encodeMatrix]; exact hdet⟩

@[simp] theorem atlasMatrix_encode (m : Matrix coordinate coordinate ℚ)
    (h : IsAtlasMatrix degree m) (hdet : m.det ≠ 0) :
    atlasMatrix (encode m h hdet) = m :=
  decodeMatrix_encodeMatrix m h

/-- The label of an honest stable presentation with nonsingular length
matrix. -/
noncomputable def encodePresentation {data : GluingDatum target degree}
    (presentation : data.LengthMatrixPresentation coordinate)
    (hnodup : ∀ row, (presentation.path row).Nodup)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix presentation).det ≠ 0) :
    chart coordinate degree :=
  encode _ (matrix_isAtlasMatrix_of_nodup presentation hnodup) hdet

@[simp] theorem atlasMatrix_encodePresentation {data : GluingDatum target degree}
    (presentation : data.LengthMatrixPresentation coordinate)
    (hnodup : ∀ row, (presentation.path row).Nodup)
    (hdet : (GluingDatum.LengthMatrixPresentation.matrix presentation).det ≠ 0) :
    atlasMatrix (encodePresentation presentation hnodup hdet) =
      GluingDatum.LengthMatrixPresentation.matrix presentation :=
  atlasMatrix_encode _ _ hdet

end DraismaVargas.LocalCases.MatrixAtlas
