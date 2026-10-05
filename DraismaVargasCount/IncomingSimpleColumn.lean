module

public import DraismaVargasCount.TrivalentWeight

@[expose] public section

/-!
# The lower half of `lemma-edge-deno` (b) on the two distinguished incoming rows

**Source.**  Vargas, Part II (arXiv:2609.09109), `lemma-edge-deno` case (b) and
`prop-signed-mult` (1) with its proof; Draisma--Vargas Part I (arXiv:1909.12924),
case `{w2-r2-nd3-M-1k}`, Figure 33 and Equation (7).  Part II justifies case (b)
by the observation that every entry in row `i` is an integer multiple of `1/k`;
that observation gives `d_i ∣ k`, and the reverse divisibility `k ∣ d_i` is what
this module supplies for the two rows that Part II's representative computation
uses.

## The point

`Count.TrivalentWeight.dvd_incomingRowDenominator_of_occurrences_eq_singleton`
asks for a **simple column**: a target direction over which the row displays
exactly one surviving occurrence.  On the incoming rows `h₂` and `h₃` of the
M-1k limit that is not available, and this is not a shortcoming of the censuses:
`W2M1kCommonBalance.double_matrix_decomposition` splits the `t₂` fibre as
`{e₁, e₂}` plus `backgroundOccurrences`, and the background part of that fibre
is nonempty exactly when the stable row returns to the wall through another
wall block.  That is the paper's global `pass-once` condition (Part II,
`def-auxiliary-conditions`), not a local census fact; see "What is
NOT proved".

**A simple column is not needed.**  The wall vertex is divalent, so the two old
wall columns carry the *same* background on every row -- Figure 33's
`σ₀(J₀,2) = σ₀(J₀,3) = s`, proved unconditionally as
`W2M1kCommonBalance.background_sum_eq` -- and the background cancels in their
difference.  `double_sub_single_eq` computes that difference on every incoming
row: it is `[h = h₁] + ([h = h₂] - [h = h₃])/k`, with no background term at all.
Evaluating it on `h₂` and on `h₃` gives an integer plus `±1/k`, and a row's
common denominator clears both entries, hence clears `±1/k`, hence is a multiple
of `k`.  One geometric hypothesis -- that `e₂` and `e₃` lie on **different**
incoming stable rows -- replaces both simple columns, on both rows at once.

## What is proved

* `dvd_of_integral_unit_fraction`, `dvd_incomingRowDenominator_of_columns_sub`,
  `dvd_incomingRowDenominator_of_column` -- **general, case-independent**: if two
  entries of one row of `StableSourceMatrix.matrix` differ by an integer plus
  `±1/k` then `k ∣ incomingRowDenominator`, and likewise for a single entry of
  that shape.  These are the rectangular replacements for the simple-column
  half of `lemma-edge-deno` (b), and they are stated over the shared
  `StableSourceMatrix` / `incomingRowDenominator` interface, not over any case.
* `double_sub_single_eq` -- **unconditional on the M-1k datum**: the two old
  wall columns of `A₀` differ by `[h₁] + ([h₂] - [h₃])/k`.  Hypotheses: exactly
  `W2M1kSourceCandidates`' bundle (a `W2R2SourceProfile.SourceProfile`, a
  `Shape`, and the `SecondEquation.W2SourceInput` the background needs).
* `k_dvd_incomingRowDenominator_secondRow`, `k_dvd_incomingRowDenominator_thirdRow`
  -- `k ∣ d₀(h₂)` and `k ∣ d₀(h₃)`, from `secondRow profile ≠ thirdRow profile`
  alone.
* `mem_occurrences_double_iff`, `mem_occurrences_single_iff` -- **what the two
  fibres really are**, at set level and unconditionally: above `t₂` a row
  displays `e₁` exactly on `h₁`, `e₂` exactly on `h₂`, and otherwise only
  background; above `t₃` it displays `e₃` exactly on `h₃`, and otherwise only
  background.  Cardinality M's dangling `e₄` never appears, being in no stable
  row.
* `occurrences_secondRow_eq_singleton`, `occurrences_thirdRow_eq_singleton` --
  the simple columns themselves, each from its own emptiness hypothesis
  (and, on `h₂`, from `h₁ ≠ h₂`), together with the divisibilities they give
  (`k_dvd_incomingRowDenominator_secondRow_of_simple` and its `thirdRow` twin).
  `k_dvd_incomingRowDenominator_secondRow_of_background` shows even that route
  never needs `h₁ ≠ h₂`: `e₁` has index one, so sharing `h₂` is harmless.
* `incomingRowDenominator_secondRow_eq`, `incomingRowDenominator_thirdRow_eq`
  and their `_of_index` forms -- **the sharp `d₀ = k`**, combining the above
  with the upper half.
* `sum_signedMult_canonical_eq_zero_of_rows_ne` -- `prop-signed-mult` (1) on the
  family `W2M1kLimitColumns.limitColumns` actually builds, with
  `Count.TrivalentWeight`'s two sharp-denominator hypotheses replaced by one
  row-distinctness hypothesis and the two upper halves.

## What is NOT proved: the hypotheses that remain explicit

* **`secondRow profile ≠ thirdRow profile`.**  Equivalently: the stable row of
  `e₂` does not run back into the wall and out along `t₃`.  This is the local
  shadow of Part II's `pass-once` condition, which holds for full-rank
  change-minimal morphisms and is inherited at limits
  (`lm:properties`, `lm:properties-inherit`).  It is proved
  through `Count.RowGeodesic`: `RowGeodesic.secondRow_ne_thirdRow_of_genusZero`
  discharges it from `graph_connected target`, `genus target = 0`,
  `DanglingEdgeNoGlue data` and `RowRamificationAtMostOne data (secondRow
  profile)`, by the ordered walk of a stable row that `Count.RowWalk` and
  `Count.TargetGeodesic` build.  This module cannot call it -- `RowGeodesic`
  imports this module, not the other way -- so it is carried here as an
  explicit hypothesis, and `genus target = 0` *is* used, at that call site:
  `sum_signedMult_canonical_eq_zero_of_rows_ne`'s `hRows` is exactly this
  hypothesis, discharged from the `hConnected`/`hGenus` the statement already
  carries.  It is the same input as the `hPairs` hypothesis of
  `Count.IndexPattern.not_two_transitions_on_one_row`.
* **The upper half `d₀ ∣ k`**, equivalently `∀ e ∈ incomingRowEdges data h,
  sourceEdgeIndex e ∣ k` (produced by `RowRegrowth` and `OutgoingRowCalculus`).
  Supplied as a hypothesis to `incomingRowDenominator_*_eq` and `*_of_index`.
* **Emptiness of `backgroundOccurrences`** on either row: supplied as a
  hypothesis wherever it is used, and never derived.
* Nothing here is conditional on integrality, on the genus, on the degree, or
  on nonsingularity of any member.

## Non-vacuity

`unit_fraction_witness` inhabits the arithmetic kernel at concrete numbers.
Every M-1k statement is about the actual `W2R2SourceProfile.SourceProfile` /
`W2M1kSourceCandidates.Shape` of the case -- no abstract family is introduced,
and no structure is defined here -- and
`sum_signedMult_canonical_eq_zero_of_rows_ne` is stated on the concrete family
`W2M1kLimitColumns.limitColumns`, which `W2M1kLimitColumns.nonempty_limitColumns`
inhabits unconditionally in both orientations.

## Consumers

The sharp incoming denominators of the multiplicity balance of the M-1k family
(`Count.TrivalentWeight.sum_signedMult_canonical_eq_zero`) and of the other wall
types (§1 is case-independent and §2--§3 transcribe for any **divalent** wall).
-/

namespace DraismaVargas.Count.IncomingSimpleColumn

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.Count.TrivalentWeight
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W2M1kCommonBalance
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.StableSourceMatrix
open DraismaVargas.LocalCases.W2M1kSourceCandidates

/-! ## 1. Generic: a row whose columns differ by a unit fraction -/

theorem integral_sub {a b : ℚ} (ha : Integral a) (hb : Integral b) : Integral (a - b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x - y, by push_cast; ring⟩

/-- **The arithmetic kernel.**  If `d · q` is an integer and `q` is an integer
plus `±1/k`, then `k ∣ d`. -/
theorem dvd_of_integral_unit_fraction {d k : ℕ} (hk : 0 < k) {c e : ℤ} (he : e = 1 ∨ e = -1)
    {q : ℚ} (hq : q = (c : ℚ) + (e : ℚ) / (k : ℚ)) (hInt : Integral ((d : ℚ) * q)) :
    k ∣ d := by
  obtain ⟨z, hz⟩ := hInt
  have hk' : (k : ℚ) ≠ 0 := by
    exact_mod_cast hk.ne'
  rw [hq] at hz
  refine natCast_dvd_of_integral_div hk ⟨e * (z - (d : ℤ) * c), ?_⟩
  rcases he with rfl | rfl
  · push_cast at hz ⊢
    field_simp at hz ⊢
    linarith
  · push_cast at hz ⊢
    field_simp at hz ⊢
    linarith

/-- Non-vacuity of the arithmetic kernel: `6 · (2 + 1/3) = 14`, so `3 ∣ 6`. -/
theorem unit_fraction_witness : (3 : ℕ) ∣ 6 :=
  dvd_of_integral_unit_fraction (d := 6) (k := 3) (by norm_num) (c := 2) (e := 1)
    (Or.inl rfl) (q := 2 + 1 / 3) (by norm_num) ⟨14, by norm_num⟩

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- **A row needs no simple column.**  If two entries of one incoming row
differ by an integer plus `±1/k`, then `k` divides that row's denominator. -/
theorem dvd_incomingRowDenominator_of_columns_sub (path : StablePath data)
    (first second : target.edges) {k : ℕ} (hk : 0 < k) {c e : ℤ} (he : e = 1 ∨ e = -1)
    (hSub : StableSourceMatrix.matrix data path first -
        StableSourceMatrix.matrix data path second = (c : ℚ) + (e : ℚ) / (k : ℚ)) :
    k ∣ incomingRowDenominator data path := by
  refine dvd_of_integral_unit_fraction hk he hSub ?_
  rw [mul_sub]
  exact integral_sub
    (integral_commonDenominator_mul Finset.univ
      (fun place ↦ StableSourceMatrix.matrix data path place) (Finset.mem_univ first))
    (integral_commonDenominator_mul Finset.univ
      (fun place ↦ StableSourceMatrix.matrix data path place) (Finset.mem_univ second))

/-- The one-column form, for a row that does have a simple column. -/
theorem dvd_incomingRowDenominator_of_column (path : StablePath data) (place : target.edges)
    {k : ℕ} (hk : 0 < k) {c e : ℤ} (he : e = 1 ∨ e = -1)
    (hCol : StableSourceMatrix.matrix data path place = (c : ℚ) + (e : ℚ) / (k : ℚ)) :
    k ∣ incomingRowDenominator data path := by
  refine dvd_of_integral_unit_fraction hk he hCol ?_
  exact integral_commonDenominator_mul Finset.univ
    (fun place ↦ StableSourceMatrix.matrix data path place) (Finset.mem_univ place)


/-! ## 2. The two wall columns of the M-1k incoming datum, differenced -/

section M1k

variable {wall : target.V} {star : TwoStar target wall} {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)

/-- **The background cancels in the difference of the two wall columns.**
On every incoming stable row, the `t₂` column minus the `t₃` column of `A₀` is
carried by the three distinguished occurrences alone: Figure 33's `s` appears
with the same coefficient in both columns
(`W2M1kCommonBalance.background_sum_eq`) and drops out. -/
theorem double_sub_single_eq (input : W2SourceInput data star) (shape : Shape profile)
    (path : StablePath data) :
    StableSourceMatrix.matrix data path (star.edge profile.doubleLabel) -
        StableSourceMatrix.matrix data path (star.edge profile.singleLabel) =
      (if path = firstRow profile then (1 : ℚ) else 0) +
        ((if path = secondRow profile then (1 : ℚ) else 0) -
          (if path = thirdRow profile then (1 : ℚ) else 0)) / (shape.k : ℚ) := by
  have hk : (1 : ℚ) < (shape.k : ℚ) := one_lt_k_cast profile shape
  have hk0 : (shape.k : ℚ) ≠ 0 := by positivity
  rw [double_matrix_decomposition profile path, single_matrix_decomposition profile path,
    first_index_cast profile shape, second_index_cast profile shape,
    third_index_cast profile shape,
    background_sum_eq profile input path profile.doubleLabel profile.singleLabel]
  field_simp
  ring


/-! ## 3. `k ∣ d₀` on the two distinguished rows -/

/-- **The lower half of `lemma-edge-deno` (b) on `e₂`'s incoming row**, from
the column difference alone.  No emptiness of the background and no simple
column is used; the only geometric input is that `e₂` and `e₃` lie on
different incoming stable rows. -/
theorem k_dvd_incomingRowDenominator_secondRow (input : W2SourceInput data star)
    (shape : Shape profile) (hRows : secondRow profile ≠ thirdRow profile) :
    shape.k ∣ incomingRowDenominator data (secondRow profile) := by
  have hk : 0 < shape.k := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt shape.one_lt_k)
  have hDiff := double_sub_single_eq profile input shape (secondRow profile)
  rw [ite_eq_left rfl, ite_eq_right hRows] at hDiff
  by_cases hFirst : secondRow profile = firstRow profile
  · rw [ite_eq_left hFirst] at hDiff
    refine dvd_incomingRowDenominator_of_columns_sub (c := 1) (e := 1) _
      (star.edge profile.doubleLabel) (star.edge profile.singleLabel) hk (Or.inl rfl) ?_
    rw [hDiff]
    push_cast
    ring
  · rw [ite_eq_right hFirst] at hDiff
    refine dvd_incomingRowDenominator_of_columns_sub (c := 0) (e := 1) _
      (star.edge profile.doubleLabel) (star.edge profile.singleLabel) hk (Or.inl rfl) ?_
    rw [hDiff]
    push_cast
    ring

/-- **The lower half of `lemma-edge-deno` (b) on `e₃`'s incoming row**, from the
same column difference and the same single hypothesis. -/
theorem k_dvd_incomingRowDenominator_thirdRow (input : W2SourceInput data star)
    (shape : Shape profile) (hRows : secondRow profile ≠ thirdRow profile) :
    shape.k ∣ incomingRowDenominator data (thirdRow profile) := by
  have hk : 0 < shape.k := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt shape.one_lt_k)
  have hDiff := double_sub_single_eq profile input shape (thirdRow profile)
  rw [ite_eq_left rfl, ite_eq_right (Ne.symm hRows)] at hDiff
  by_cases hFirst : thirdRow profile = firstRow profile
  · rw [ite_eq_left hFirst] at hDiff
    refine dvd_incomingRowDenominator_of_columns_sub (c := 1) (e := -1) _
      (star.edge profile.doubleLabel) (star.edge profile.singleLabel) hk (Or.inr rfl) ?_
    rw [hDiff]
    push_cast
    ring
  · rw [ite_eq_right hFirst] at hDiff
    refine dvd_incomingRowDenominator_of_columns_sub (c := 0) (e := -1) _
      (star.edge profile.doubleLabel) (star.edge profile.singleLabel) hk (Or.inr rfl) ?_
    rw [hDiff]
    push_cast
    ring


/-! ## 4. What the fibre over a wall column really is -/

private theorem occ_iff {path : StablePath data} (edge : NonDanglingEdge data)
    {place : target.edges} (hTarget : edge.1.1.1 = place) :
    edge.1 ∈ occurrences data path place ↔ path = edge.stablePath := by
  rw [mem_occurrences]
  exact ⟨fun h ↦ h.1.choose_spec.symm, fun h ↦ ⟨⟨edge.2, h.symm⟩, hTarget⟩⟩

private theorem selected_double_eq' {path : StablePath data} (edge : data.SourceEdge)
    (hMem : edge ∈ occurrences data path (star.edge profile.doubleLabel))
    (hRel : (data.vertexPartition wall).Rel block.1 edge.1.2) :
    edge = profile.first.1 ∨ edge = profile.second.1 := by
  obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
  have hIncident : Incident data edge (WallBlock.sourceVertex data wall block) := by
    apply (incident_iff_target_mem_and_rel data edge _).mpr
    refine ⟨hTarget ▸ star.edge_mem_incidentEdges profile.doubleLabel, ?_⟩
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr block.1) edge.1.2
    exact ((data.vertexPartition wall).rel_repr_left block.1).trans hRel
  rcases profile.exhaustive ⟨edge, hIncident⟩ with hEq | hEq | hEq | hEq
  · exact Or.inl (congrArg Subtype.val hEq)
  · exact Or.inr (congrArg Subtype.val hEq)
  · exact absurd ((hTarget.symm.trans
      (congrArg (fun e : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ e.1.1.1) hEq)).trans profile.third_target)
      (star.edge_injective.ne profile.labels_ne)
  · refine absurd ?_ hSurvives
    have hDeleted : edge = profile.deleted.edge.1 := congrArg Subtype.val hEq
    rw [hDeleted]
    exact profile.deleted.dangling

private theorem selected_single_eq' {path : StablePath data} (edge : data.SourceEdge)
    (hMem : edge ∈ occurrences data path (star.edge profile.singleLabel))
    (hRel : (data.vertexPartition wall).Rel block.1 edge.1.2) :
    edge = profile.third.1 := by
  obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
  have hIncident : Incident data edge (WallBlock.sourceVertex data wall block) := by
    apply (incident_iff_target_mem_and_rel data edge _).mpr
    refine ⟨hTarget ▸ star.edge_mem_incidentEdges profile.singleLabel, ?_⟩
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr block.1) edge.1.2
    exact ((data.vertexPartition wall).rel_repr_left block.1).trans hRel
  rcases profile.exhaustive ⟨edge, hIncident⟩ with hEq | hEq | hEq | hEq
  · exact absurd ((hTarget.symm.trans
      (congrArg (fun e : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ e.1.1.1) hEq)).trans profile.first_target)
      (star.edge_injective.ne profile.labels_ne.symm)
  · exact absurd ((hTarget.symm.trans
      (congrArg (fun e : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ e.1.1.1) hEq)).trans profile.second_target)
      (star.edge_injective.ne profile.labels_ne.symm)
  · exact congrArg Subtype.val hEq
  · refine absurd ?_ hSurvives
    have hDeleted : edge = profile.deleted.edge.1 := congrArg Subtype.val hEq
    rw [hDeleted]
    exact profile.deleted.dangling

/-- **The exact `t₂` fibre of an incoming row.**  It is `e₁` on `e₁`'s row,
`e₂` on `e₂`'s row, and the background — nothing else.  This is the set-level
form of `W2M1kCommonBalance.double_matrix_decomposition`. -/
theorem mem_occurrences_double_iff (path : StablePath data) (edge : data.SourceEdge) :
    edge ∈ occurrences data path (star.edge profile.doubleLabel) ↔
      (edge = profile.first.1 ∧ path = firstRow profile) ∨
        (edge = profile.second.1 ∧ path = secondRow profile) ∨
          edge ∈ backgroundOccurrences star block path profile.doubleLabel := by
  classical
  constructor
  · intro hMem
    by_cases hRel : (data.vertexPartition wall).Rel block.1 edge.1.2
    · rcases selected_double_eq' profile edge hMem hRel with rfl | rfl
      · exact Or.inl ⟨rfl,
          (occ_iff ⟨_, profile.first_survives⟩ profile.first_target).mp hMem⟩
      · exact Or.inr (Or.inl ⟨rfl,
          (occ_iff ⟨_, profile.second_survives⟩ profile.second_target).mp hMem⟩)
    · exact Or.inr (Or.inr ((mem_backgroundOccurrences star block path _ edge).mpr ⟨hMem, hRel⟩))
  · rintro (⟨rfl, hPath⟩ | ⟨rfl, hPath⟩ | hBg)
    · exact (occ_iff ⟨_, profile.first_survives⟩ profile.first_target).mpr hPath
    · exact (occ_iff ⟨_, profile.second_survives⟩ profile.second_target).mpr hPath
    · exact ((mem_backgroundOccurrences star block path _ edge).mp hBg).1

/-- **The exact `t₃` fibre of an incoming row.**  Only `e₃` and the background:
Cardinality M's dangling `e₄` lies above `t₃` but is in no stable row. -/
theorem mem_occurrences_single_iff (path : StablePath data) (edge : data.SourceEdge) :
    edge ∈ occurrences data path (star.edge profile.singleLabel) ↔
      (edge = profile.third.1 ∧ path = thirdRow profile) ∨
        edge ∈ backgroundOccurrences star block path profile.singleLabel := by
  classical
  constructor
  · intro hMem
    by_cases hRel : (data.vertexPartition wall).Rel block.1 edge.1.2
    · have hEq := selected_single_eq' profile edge hMem hRel
      subst hEq
      exact Or.inl ⟨rfl, (occ_iff ⟨_, profile.third_survives⟩ profile.third_target).mp hMem⟩
    · exact Or.inr ((mem_backgroundOccurrences star block path _ edge).mpr ⟨hMem, hRel⟩)
  · rintro (⟨rfl, hPath⟩ | hBg)
    · exact (occ_iff ⟨_, profile.third_survives⟩ profile.third_target).mpr hPath
    · exact ((mem_backgroundOccurrences star block path _ edge).mp hBg).1

/-! ### The simple column, and exactly what it costs -/

/-- **The simple column on `e₂`'s row**, from the two facts that make it
simple: `e₁` is on another row, and the background is empty there. -/
theorem occurrences_secondRow_eq_singleton
    (hFirstRow : firstRow profile ≠ secondRow profile)
    (hBackground :
      backgroundOccurrences star block (secondRow profile) profile.doubleLabel = ∅) :
    occurrences data (secondRow profile) (star.edge profile.doubleLabel) =
      {profile.second.1} := by
  classical
  ext edge
  rw [mem_occurrences_double_iff profile, Finset.mem_singleton]
  constructor
  · rintro (⟨-, hPath⟩ | ⟨hEq, -⟩ | hBg)
    · exact absurd hPath.symm hFirstRow
    · exact hEq
    · exact absurd (hBackground ▸ hBg) (Finset.notMem_empty edge)
  · rintro rfl
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- **The simple column on `e₃`'s row.**  Here the background is the only
obstruction: nothing else of `A₀` lies above `t₃` in a stable row. -/
theorem occurrences_thirdRow_eq_singleton
    (hBackground :
      backgroundOccurrences star block (thirdRow profile) profile.singleLabel = ∅) :
    occurrences data (thirdRow profile) (star.edge profile.singleLabel) =
      {profile.third.1} := by
  classical
  ext edge
  rw [mem_occurrences_single_iff profile, Finset.mem_singleton]
  constructor
  · rintro (⟨hEq, -⟩ | hBg)
    · exact hEq
    · exact absurd (hBackground ▸ hBg) (Finset.notMem_empty edge)
  · rintro rfl
    exact Or.inl ⟨rfl, rfl⟩



/-- An empty background makes Figure 33's `s` vanish on that row. -/
theorem backgroundColumn_eq_zero (path : StablePath data) (label : Fin 2)
    (hBackground : backgroundOccurrences star block path label = ∅) :
    backgroundColumn star block path label = 0 := by
  rw [backgroundColumn, hBackground, Finset.sum_empty]

/-- **The background route, sharpened.**  Only the background has to vanish;
`e₁` may share `e₂`'s row without harm, since its index is one.  So the
simple column proper is never the thing that is needed. -/
theorem k_dvd_incomingRowDenominator_secondRow_of_background (shape : Shape profile)
    (hBackground :
      backgroundOccurrences star block (secondRow profile) profile.doubleLabel = ∅) :
    shape.k ∣ incomingRowDenominator data (secondRow profile) := by
  have hk : 0 < shape.k := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt shape.one_lt_k)
  have hk0 : (shape.k : ℚ) ≠ 0 := by
    exact_mod_cast hk.ne'
  have hCol := double_matrix_decomposition profile (secondRow profile)
  rw [ite_eq_left rfl, first_index_cast profile shape, second_index_cast profile shape,
    backgroundColumn_eq_zero (secondRow profile) profile.doubleLabel hBackground] at hCol
  by_cases hFirst : secondRow profile = firstRow profile
  · rw [ite_eq_left hFirst] at hCol
    refine dvd_incomingRowDenominator_of_column (c := 1) (e := 1) _
      (star.edge profile.doubleLabel) hk (Or.inl rfl) ?_
    rw [hCol]
    push_cast
    ring
  · rw [ite_eq_right hFirst] at hCol
    refine dvd_incomingRowDenominator_of_column (c := 0) (e := 1) _
      (star.edge profile.doubleLabel) hk (Or.inl rfl) ?_
    rw [hCol]
    push_cast
    ring

/-- The same on `e₃`'s row, where the background is the only obstruction. -/
theorem k_dvd_incomingRowDenominator_thirdRow_of_background (shape : Shape profile)
    (hBackground :
      backgroundOccurrences star block (thirdRow profile) profile.singleLabel = ∅) :
    shape.k ∣ incomingRowDenominator data (thirdRow profile) := by
  have hk : 0 < shape.k := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt shape.one_lt_k)
  have hk0 : (shape.k : ℚ) ≠ 0 := by
    exact_mod_cast hk.ne'
  have hCol := single_matrix_decomposition profile (thirdRow profile)
  rw [ite_eq_left rfl, third_index_cast profile shape,
    backgroundColumn_eq_zero (thirdRow profile) profile.singleLabel hBackground] at hCol
  refine dvd_incomingRowDenominator_of_column (c := 0) (e := 1) _
    (star.edge profile.singleLabel) hk (Or.inl rfl) ?_
  rw [hCol]
  push_cast
  ring

/-- The simple-column route, for the record: a simple column does give the lower
half, but it costs two extra facts that the column difference does not need. -/
theorem k_dvd_incomingRowDenominator_secondRow_of_simple (shape : Shape profile)
    (hFirstRow : firstRow profile ≠ secondRow profile)
    (hBackground :
      backgroundOccurrences star block (secondRow profile) profile.doubleLabel = ∅) :
    shape.k ∣ incomingRowDenominator data (secondRow profile) :=
  shape.second_index ▸ dvd_incomingRowDenominator_of_occurrences_eq_singleton
    (secondRow profile) (star.edge profile.doubleLabel)
    (occurrences_secondRow_eq_singleton profile hFirstRow hBackground)

theorem k_dvd_incomingRowDenominator_thirdRow_of_simple (shape : Shape profile)
    (hBackground :
      backgroundOccurrences star block (thirdRow profile) profile.singleLabel = ∅) :
    shape.k ∣ incomingRowDenominator data (thirdRow profile) :=
  shape.third_index ▸ dvd_incomingRowDenominator_of_occurrences_eq_singleton
    (thirdRow profile) (star.edge profile.singleLabel)
    (occurrences_thirdRow_eq_singleton profile hBackground)

/-! ## 5. The sharp incoming denominators, and `prop-signed-mult` (1) -/

/-- **`d₀(h₂) = k`**, from the column difference and the upper half. -/
theorem incomingRowDenominator_secondRow_eq (input : W2SourceInput data star)
    (shape : Shape profile) (hRows : secondRow profile ≠ thirdRow profile)
    (hUpper : incomingRowDenominator data (secondRow profile) ∣ shape.k) :
    incomingRowDenominator data (secondRow profile) = shape.k :=
  Nat.dvd_antisymm hUpper (k_dvd_incomingRowDenominator_secondRow profile input shape hRows)

/-- **`d₀(h₃) = k`**, from the same column difference and the upper half. -/
theorem incomingRowDenominator_thirdRow_eq (input : W2SourceInput data star)
    (shape : Shape profile) (hRows : secondRow profile ≠ thirdRow profile)
    (hUpper : incomingRowDenominator data (thirdRow profile) ∣ shape.k) :
    incomingRowDenominator data (thirdRow profile) = shape.k :=
  Nat.dvd_antisymm hUpper (k_dvd_incomingRowDenominator_thirdRow profile input shape hRows)

/-- The same with the upper half in the form `RowRegrowth` delivers it:
every index displayed on the row divides `k`. -/
theorem incomingRowDenominator_secondRow_eq_of_index (input : W2SourceInput data star)
    (shape : Shape profile) (hRows : secondRow profile ≠ thirdRow profile)
    (hIndex : ∀ edge ∈ incomingRowEdges data (secondRow profile),
      data.sourceEdgeIndex edge ∣ shape.k) :
    incomingRowDenominator data (secondRow profile) = shape.k :=
  incomingRowDenominator_secondRow_eq profile input shape hRows
    (incomingRowDenominator_dvd_of_forall_index_dvd _ hIndex)

theorem incomingRowDenominator_thirdRow_eq_of_index (input : W2SourceInput data star)
    (shape : Shape profile) (hRows : secondRow profile ≠ thirdRow profile)
    (hIndex : ∀ edge ∈ incomingRowEdges data (thirdRow profile),
      data.sourceEdgeIndex edge ∣ shape.k) :
    incomingRowDenominator data (thirdRow profile) = shape.k :=
  incomingRowDenominator_thirdRow_eq profile input shape hRows
    (incomingRowDenominator_dvd_of_forall_index_dvd _ hIndex)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- **`prop-signed-mult` (1) for `{w2-r2-nd3-M-1k}` with the simple-column half
discharged.**  The hypotheses are: `e₂` and `e₃` lie on different incoming
stable rows, and the two upper halves.  No statement about the background of a
wall column survives. -/
theorem sum_signedMult_canonical_eq_zero_of_rows_ne (input : W2SourceInput data star)
    (shape : Shape profile) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hRows : secondRow profile ≠ thirdRow profile)
    (hIndex2 : ∀ edge ∈ incomingRowEdges data (secondRow profile),
      data.sourceEdgeIndex edge ∣ shape.k)
    (hIndex3 : ∀ edge ∈ incomingRowEdges data (thirdRow profile),
      data.sourceEdgeIndex edge ∣ shape.k) :
    ∑ position : Fin 3, signedMult
        ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).labelling
          ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).canonicalInitialLabelling
            input) position).presentation = 0 :=
  sum_signedMult_canonical_eq_zero input shape hConnected hGenus
    (incomingRowDenominator_secondRow_eq_of_index profile input shape hRows hIndex2)
    (incomingRowDenominator_thirdRow_eq_of_index profile input shape hRows hIndex3)

end M1k

end DraismaVargas.Count.IncomingSimpleColumn
