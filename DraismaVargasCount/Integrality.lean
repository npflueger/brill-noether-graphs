import DraismaVargasCount.EdgeDenominator
import DraismaVargasCount.FibreCaterpillar

/-!
# Integrality of the multiplicity, and the natural-number multiplicity

**Source.**  Vargas, Part II (arXiv:2609.09109), the definition of the multiplicity
(`def-multiplicity`): `Mult φ = (D_φ / 2^{l(T)}) · det A_φ`, where `D_φ` is the product of
the least common denominators of the rows of `A_φ` and `l(T)` the number of leaves of the
target.  This module proves that `Mult φ` is an integer.  The cleared matrix
`B' = diag(dᵢ) · A_φ · diag(½ on leaf columns, 1 elsewhere)` and the unconditional
determinant identity `det B' = D_φ · det A_φ · (1/2)^{#leaf columns}` are
`Count.Multiplicity`'s.

## What is proved

**All of it is unconditional on a `FullDimensionalSourcePresentation`**: no
hypothesis on the target, the degree or the genus survives.

* `noLeafToLeafEdge_of_fullDimensional` -- **no target edge of a
  full-dimensional presentation joins two leaves.**  This supplies the hypothesis
  `NoLeafToLeafEdge` of `Count.Multiplicity` and `Count.LeafFibre`, and it needs neither
  connectivity nor an edge count: if `t` joined the leaves `u` and `v` then every
  surviving occurrence above `t` would have its two endpoints at the core
  vertices `A_u` and `A_v`, both of surviving valency two; the property "lies
  above `t`" is then closed under `Consecutive` (a surviving occurrence at `A_u`
  lies above `t`, `LeafFibre.mem_leafSurvivors_of_incident_coreVertex`), so the
  whole stable path of such an occurrence lies above `t` and has no path end,
  contradicting `fd.pathEnds`.
* Consequently `leafColumns_card_eq_leafCount_of_fullDimensional` and the
  hypothesis-free `fdAbsMult_eq_abs_det_clearedMatrix'`.
* `clearedMatrix_leafColumn` -- **the leaf columns of `B'` are the standard
  basis vectors** `e_{h(v)}`: `LeafFibre.matrix_leafEdge_column` gives `2` on
  row `h(v)`, `EdgeDenominator.rowDenominator_eq_one_of_leafRow` gives
  `d_{h(v)} = 1`, and the halving turns `2` into `1`.
* `clearedMatrix_integral`, `clearedMatrixInt`, `clearedMatrixInt_cast`,
  `det_clearedMatrix_eq_cast` -- **`B'` is an integer matrix**, and its
  determinant is the cast of an integer determinant.  Off the leaf columns the
  entry is `dᵢ · A_φ(i,t)`, integral because `dᵢ` is by definition the least
  common denominator of row `i` (`Denominator.integral_commonDenominator_mul`);
  the row denominators are used only through that, so this half needs no index
  pattern at all.
* `signedMult_eq_det_clearedMatrix` -- `Mult φ = det B'` on the nose (not just
  up to sign), and hence **`isIntegralMultiplicity`**: `Count.Multiplicity`'s
  predicate `IsIntegralMultiplicity` is a theorem with no hypotheses.
* `absMultNat`, `fdAbsMultNat` -- the **natural-number multiplicity**, with
  `absMult_eq_absMultNat`, `fdAbsMult_eq_fdAbsMultNat` and
  `fdAbsMultNat_pos`.
* `hasOddMult_iff_odd_fdAbsMultNat` -- **the oddness bridge**: the
  existential `FibreMember.HasOddMult` (`∃ k : ℕ, Odd k ∧ absMult = k`) is
  equivalent to `Odd (fdAbsMultNat member.fullDim)`.  The definition of `HasOddMult` is
  unchanged; `FibreMember.oddMult` is the natural number itself.

## What is not proved here

* The trichotomy of `Count.EdgeDenominator` is *not* used for the integrality
  of the non-leaf columns; only case (a) (`d_{h(v)} = 1`, unconditional) is
  used, and only to sharpen the leaf column from `d_{h(v)} · e_{h(v)}` to
  `e_{h(v)}`.  So no part of this module inherits
  `EdgeDenominator.RowIndicesConsecutive`.
* Nothing here is about the descent of `absMult` to the fibre quotient.
  `Count.Fibre.AbsMultDescends` names that statement, and
  `Count.TransportMultiplicity.absMultDescends` proves it unconditionally; this
  module neither uses nor supplies it.
* Nothing here says any particular multiplicity is odd; it says the
  multiplicity is a natural number, so that oddness can be stated of it.

## Consumers

The oddness bridge lets `FibreMember.HasOddMult` be read as oddness of a natural number.
The balancing identities at walls and the equality of signed multiplicities across a
non-trivalent limit consume `signedMult ∈ ℤ`, and the odd multiplicity of a member is
what the endgame (step 5 of `Assembly`) descends to an odd subdivision.
-/

namespace DraismaVargas.Count

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.LeafFibre

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1.  No target edge joins two leaves -/

/-- A target edge occurrence never joins a vertex to itself: the target graph
is loopless. -/
theorem targetEdge_fst_ne_snd (item : target.edges) :
    (item : target.V × target.V).1 ≠ (item : target.V × target.V).2 := by
  intro hEq
  have hMem : (item : target.V × target.V) ∈ target.edges := Multiset.coe_mem
  have hPair : (item : target.V × target.V) =
      ((item : target.V × target.V).1, (item : target.V × target.V).1) :=
    Prod.ext rfl hEq.symm
  rw [hPair] at hMem
  exact target.loopless _ hMem

/-- **No target edge of a full-dimensional presentation joins two leaves.**
The two surviving occurrences above such an edge would run between the two core
vertices `A_u`, `A_v`, both of surviving valency two, and the whole stable path
through them would stay above that one edge: a stable cycle, which `pathEnds`
forbids. -/
theorem noLeafToLeafEdge_of_fullDimensional
    (fd : FullDimensionalSourcePresentation data coordinate) :
    NoLeafToLeafEdge target := by
  classical
  intro item hFirst hSecond
  have hEdgeFirst : item = leafEdge hFirst :=
    eq_leafEdge_of_mem hFirst
      ((GluingContraction.mem_incidentEdges_iff _ _).mpr (Or.inl rfl))
  have hEdgeSecond : item = leafEdge hSecond :=
    eq_leafEdge_of_mem hSecond
      ((GluingContraction.mem_incidentEdges_iff _ _).mpr (Or.inr rfl))
  have hCoreNe : coreVertex fd hFirst ≠ coreVertex fd hSecond := by
    intro hEq
    exact targetEdge_fst_ne_snd item
      (((coreVertex_target fd hFirst).symm.trans (congrArg (fun w ↦ w.1.1) hEq)).trans
        (coreVertex_target fd hSecond))
  -- every vertex met by a surviving occurrence above `item` is one of the cores
  have key : ∀ x : data.SourceEdge, ¬ IsDangling data x → x.1.1 = item →
      ∀ w : data.SourceVertex, Incident data x w →
        w = coreVertex fd hFirst ∨ w = coreVertex fd hSecond := by
    intro x hSurvives hTarget w hIncident
    have hMemFirst : x ∈ leafSurvivors (data := data) hFirst :=
      (mem_leafSurvivors hFirst).mpr ⟨hSurvives, hTarget.trans hEdgeFirst⟩
    have hMemSecond : x ∈ leafSurvivors (data := data) hSecond :=
      (mem_leafSurvivors hSecond).mpr ⟨hSurvives, hTarget.trans hEdgeSecond⟩
    have hIncFirst := incident_coreVertex_of_mem_leafSurvivors fd hFirst hMemFirst
    have hIncSecond := incident_coreVertex_of_mem_leafSurvivors fd hSecond hMemSecond
    rcases hIncFirst with h1 | h1 <;> rcases hIncSecond with h2 | h2 <;>
      rcases hIncident with h3 | h3
    · exact absurd (h1.symm.trans h2) hCoreNe
    · exact absurd (h1.symm.trans h2) hCoreNe
    · exact Or.inl (h3.symm.trans h1)
    · exact Or.inr (h3.symm.trans h2)
    · exact Or.inr (h3.symm.trans h2)
    · exact Or.inl (h3.symm.trans h1)
    · exact absurd (h1.symm.trans h2) hCoreNe
    · exact absurd (h1.symm.trans h2) hCoreNe
  -- "lies above `item`" is closed along stable paths
  have hClosed : ∀ one two : NonDanglingEdge data, Consecutive data one two →
      one.1.1.1 = item → two.1.1.1 = item := by
    rintro one two ⟨-, w, hIncOne, hIncTwo, -⟩ hOne
    rcases key one.1 one.2 hOne w hIncOne with hw | hw
    · exact ((mem_leafSurvivors hFirst).mp (mem_leafSurvivors_of_incident_coreVertex fd
        hFirst two.2 (by rw [← hw]; exact hIncTwo))).2.trans hEdgeFirst.symm
    · exact ((mem_leafSurvivors hSecond).mp (mem_leafSurvivors_of_incident_coreVertex fd
        hSecond two.2 (by rw [← hw]; exact hIncTwo))).2.trans hEdgeSecond.symm
  obtain ⟨seed, hSeedTarget, hSeedSurvives⟩ := fd.noDanglingTargetFibres item
  obtain ⟨first, w, hPathEq, hIncident, hValency⟩ :=
    fd.pathEnds (⟨seed, hSeedSurvives⟩ : NonDanglingEdge data)
  have hFirstTarget : first.1.1.1 = item :=
    (eqvGen_iff_of_closed hClosed ((stablePath_eq_iff first
      (⟨seed, hSeedSurvives⟩ : NonDanglingEdge data)).mp hPathEq)).mpr hSeedTarget
  rcases key first.1 first.2 hFirstTarget w hIncident with hw | hw
  · exact hValency (by rw [hw]; exact nonDanglingValency_coreVertex fd hFirst)
  · exact hValency (by rw [hw]; exact nonDanglingValency_coreVertex fd hSecond)

/-- **The leaf columns are in bijection with the leaves**, with no hypothesis. -/
theorem leafColumns_card_eq_leafCount_of_fullDimensional
    (fd : FullDimensionalSourcePresentation data coordinate) :
    (leafColumns fd.labelling.presentation).card = leafCount target :=
  leafColumns_card_eq_leafCount _ (noLeafToLeafEdge_of_fullDimensional fd)

/-- **The workhorse identity, with nothing left to discharge**:
`absMult φ = |det B'|` for every full-dimensional presentation. -/
theorem fdAbsMult_eq_abs_det_clearedMatrix'
    (fd : FullDimensionalSourcePresentation data coordinate) :
    fdAbsMult fd = |(fdClearedMatrix fd).det| :=
  absMult_eq_abs_det_clearedMatrix _ (leafColumns_card_eq_leafCount_of_fullDimensional fd)

/-! ## 2.  The leaf columns of the cleared matrix -/

/-- The column carrying the edge at a leaf really is a leaf column. -/
theorem leafEdge_column_mem_leafColumns
    (fd : FullDimensionalSourcePresentation data coordinate) {vertex : target.V}
    (hLeaf : IsLeafVertex target vertex) :
    fd.labelling.targetEdge.symm (leafEdge hLeaf) ∈
      leafColumns fd.labelling.presentation := by
  refine (mem_leafColumns _ _).mpr ⟨vertex, hLeaf, ?_⟩
  rw [show fd.labelling.presentation.targetEdge = fd.labelling.targetEdge from rfl,
    Equiv.apply_symm_apply]
  exact leafEdge_mem hLeaf

/-- Conversely, every leaf column carries the edge at some leaf. -/
theorem exists_leaf_of_mem_leafColumns
    (fd : FullDimensionalSourcePresentation data coordinate) {column : coordinate}
    (hColumn : column ∈ leafColumns fd.labelling.presentation) :
    ∃ (vertex : target.V) (hLeaf : IsLeafVertex target vertex),
      column = fd.labelling.targetEdge.symm (leafEdge hLeaf) := by
  obtain ⟨vertex, hLeaf, hMem⟩ := (mem_leafColumns _ _).mp hColumn
  refine ⟨vertex, hLeaf, ?_⟩
  rw [← eq_leafEdge_of_mem hLeaf hMem]
  exact (Equiv.symm_apply_apply _ _).symm

/-- **The leaf column of `B'` is the standard basis vector `e_{h(v)}`.**  The
`A_φ` column is `2 · e_{h(v)}` (`LeafFibre.matrix_leafEdge_column`), the row
denominator `d_{h(v)}` is `1` (`EdgeDenominator`, case (a) of
`lemma-edge-deno`), and the leaf-column scaling halves the `2`. -/
theorem clearedMatrix_leafColumn
    (fd : FullDimensionalSourcePresentation data coordinate) {vertex : target.V}
    (hLeaf : IsLeafVertex target vertex) (sourceRow : coordinate) :
    clearedMatrix fd.labelling.presentation sourceRow
        (fd.labelling.targetEdge.symm (leafEdge hLeaf)) =
      if sourceRow = leafRow fd hLeaf then 1 else 0 := by
  classical
  rw [clearedMatrix_apply, matrix_leafEdge_column fd hLeaf sourceRow,
    columnScale, if_pos (leafEdge_column_mem_leafColumns fd hLeaf)]
  by_cases hCase : sourceRow = leafRow fd hLeaf
  · rw [if_pos hCase, if_pos hCase, hCase,
      EdgeDenominator.rowDenominator_eq_one_of_leafRow fd hLeaf]
    norm_num
  · rw [if_neg hCase, if_neg hCase]
    ring

/-! ## 3.  The cleared matrix is an integer matrix -/

/-- **Every entry of `B'` is an integer.**  Off the leaf columns this is the
defining property of the row denominator; on a leaf column it is the previous
theorem. -/
theorem clearedMatrix_integral
    (fd : FullDimensionalSourcePresentation data coordinate)
    (sourceRow column : coordinate) :
    Integral (clearedMatrix fd.labelling.presentation sourceRow column) := by
  classical
  by_cases hColumn : column ∈ leafColumns fd.labelling.presentation
  · obtain ⟨vertex, hLeaf, rfl⟩ := exists_leaf_of_mem_leafColumns fd hColumn
    rw [clearedMatrix_leafColumn fd hLeaf sourceRow]
    by_cases hCase : sourceRow = leafRow fd hLeaf
    · exact ⟨1, by rw [if_pos hCase]; norm_num⟩
    · exact ⟨0, by rw [if_neg hCase]; norm_num⟩
  · rw [clearedMatrix_apply, columnScale, if_neg hColumn, mul_one]
    exact integral_commonDenominator_mul _ _ (Finset.mem_univ column)

/-- `B'` as a matrix of integers. -/
noncomputable def clearedMatrixInt
    (fd : FullDimensionalSourcePresentation data coordinate) :
    Matrix coordinate coordinate ℤ := fun sourceRow column ↦
  (clearedMatrix fd.labelling.presentation sourceRow column).num

@[simp] theorem clearedMatrixInt_cast
    (fd : FullDimensionalSourcePresentation data coordinate)
    (sourceRow column : coordinate) :
    ((clearedMatrixInt fd sourceRow column : ℤ) : ℚ) =
      clearedMatrix fd.labelling.presentation sourceRow column := by
  obtain ⟨value, hValue⟩ := clearedMatrix_integral fd sourceRow column
  rw [clearedMatrixInt, hValue, Rat.num_intCast]

theorem mapMatrix_clearedMatrixInt
    (fd : FullDimensionalSourcePresentation data coordinate) :
    (Int.castRingHom ℚ).mapMatrix (clearedMatrixInt fd) =
      clearedMatrix fd.labelling.presentation := by
  funext sourceRow column
  exact clearedMatrixInt_cast fd sourceRow column

/-- **`det B'` is the cast of an integer determinant.** -/
theorem det_clearedMatrix_eq_cast
    (fd : FullDimensionalSourcePresentation data coordinate) :
    (clearedMatrix fd.labelling.presentation).det =
      (((clearedMatrixInt fd).det : ℤ) : ℚ) := by
  conv_lhs => rw [← mapMatrix_clearedMatrixInt fd]
  exact (RingHom.map_det (Int.castRingHom ℚ) (clearedMatrixInt fd)).symm

/-! ## 4.  Integrality of the multiplicity, and `absMultNat` -/

/-- **`Mult φ = det B'` on the nose**, once the leaf columns are counted by the
leaves.  `Count.Multiplicity.absMult_eq_abs_det_clearedMatrix` is its absolute
value. -/
theorem signedMult_eq_det_clearedMatrix
    (presentation : data.LengthMatrixPresentation coordinate)
    (hLeaf : (leafColumns presentation).card = leafCount target) :
    signedMult presentation = (clearedMatrix presentation).det := by
  rw [det_clearedMatrix, hLeaf, signedMult, one_div, inv_pow, div_eq_mul_inv]
  ring

theorem fdSignedMult_eq_det_clearedMatrix
    (fd : FullDimensionalSourcePresentation data coordinate) :
    fdSignedMult fd = (((clearedMatrixInt fd).det : ℤ) : ℚ) := by
  rw [fdSignedMult, signedMult_eq_det_clearedMatrix _
    (leafColumns_card_eq_leafCount_of_fullDimensional fd), det_clearedMatrix_eq_cast]

/-- **`IsIntegralMultiplicity` is a theorem with no hypotheses.**  This is the
predicate `Count.Multiplicity` names and does not prove. -/
theorem isIntegralMultiplicity
    (fd : FullDimensionalSourcePresentation data coordinate) :
    IsIntegralMultiplicity fd.labelling.presentation :=
  ⟨(clearedMatrixInt fd).det, fdSignedMult_eq_det_clearedMatrix fd⟩

/-- The natural-number multiplicity `|Mult φ| ∈ ℕ`. -/
noncomputable def absMultNat
    (presentation : data.LengthMatrixPresentation coordinate) : ℕ :=
  (signedMult presentation).num.natAbs

/-- The natural-number multiplicity of a full-dimensional presentation. -/
noncomputable def fdAbsMultNat
    (fd : FullDimensionalSourcePresentation data coordinate) : ℕ :=
  absMultNat fd.labelling.presentation

/-- **`absMult φ = absMultNat φ`**: the multiplicity really is that natural
number. -/
theorem absMult_eq_absMultNat
    (presentation : data.LengthMatrixPresentation coordinate)
    (hIntegral : IsIntegralMultiplicity presentation) :
    absMult presentation = (absMultNat presentation : ℚ) := by
  obtain ⟨value, hValue⟩ := hIntegral
  rw [absMult, absMultNat, hValue, Rat.num_intCast]
  simp

theorem fdAbsMult_eq_fdAbsMultNat
    (fd : FullDimensionalSourcePresentation data coordinate) :
    fdAbsMult fd = (fdAbsMultNat fd : ℚ) :=
  absMult_eq_absMultNat _ (isIntegralMultiplicity fd)

/-- The natural-number multiplicity is positive: a full-dimensional
presentation is nonsingular. -/
theorem fdAbsMultNat_pos
    (fd : FullDimensionalSourcePresentation data coordinate) :
    0 < fdAbsMultNat fd := by
  refine Nat.pos_of_ne_zero fun hZero ↦ ?_
  have hAbs : fdAbsMult fd = 0 := by
    rw [fdAbsMult_eq_fdAbsMultNat, hZero]
    norm_num
  exact abs_ne_zero.mpr (fdSignedMult_ne_zero fd) hAbs

/-! ## 5.  The oddness bridge to the labelled fibre -/

section Fibre

variable {n p : ℕ} {core : Utilities.Certificate.ExplicitPotential.Core n p}
  {y : Fin p → ℚ} {degree' : ℕ}

/-- The natural-number multiplicity of a member of the labelled fibre. -/
noncomputable def FibreMember.oddMult (member : FibreMember core y degree') : ℕ :=
  fdAbsMultNat member.fullDim

theorem FibreMember.absMult_eq_oddMult (member : FibreMember core y degree') :
    member.absMult = (member.oddMult : ℚ) :=
  fdAbsMult_eq_fdAbsMultNat member.fullDim

theorem FibreMember.oddMult_pos (member : FibreMember core y degree') :
    0 < member.oddMult := fdAbsMultNat_pos member.fullDim

/-- **The oddness bridge.**  The existential `HasOddMult` is exactly
oddness of the natural-number multiplicity. -/
theorem hasOddMult_iff_odd_oddMult (member : FibreMember core y degree') :
    member.HasOddMult ↔ Odd member.oddMult := by
  constructor
  · rintro ⟨value, hOdd, hValue⟩
    have hCast : (member.oddMult : ℚ) = (value : ℚ) := by
      rw [← FibreMember.absMult_eq_oddMult, hValue]
    have hEq : member.oddMult = value := by exact_mod_cast hCast
    rw [hEq]
    exact hOdd
  · intro hOdd
    exact ⟨member.oddMult, hOdd, member.absMult_eq_oddMult⟩

/-- The same bridge written on the presentation, for consumers that do not
carry a `FibreMember`. -/
theorem hasOddMult_iff_odd_fdAbsMultNat (member : FibreMember core y degree') :
    member.HasOddMult ↔ Odd (fdAbsMultNat member.fullDim) :=
  hasOddMult_iff_odd_oddMult member

end Fibre

/-! ## 6.  Non-vacuity: the caterpillar of loops -/

namespace Integrality

open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.Count.FibreCaterpillar

/-- **Non-vacuity of `noLeafToLeafEdge_of_fullDimensional`**: derived for the
caterpillar of loops, it reproves the combinatorial
`Count.Multiplicity.Caterpillar.noLeafToLeafEdge_catTree`. -/
example (m : ℕ) : NoLeafToLeafEdge (catTree m) :=
  noLeafToLeafEdge_of_fullDimensional (CaterpillarRows.fullDim m)

/-- **Non-vacuity of integrality**: the caterpillar seed's cleared matrix is an
integer matrix, uniformly in the genus. -/
example (m : ℕ) (sourceRow column : Fin (6 * m + 3)) :
    Integral (clearedMatrix (CaterpillarRows.labelling m).presentation sourceRow column) :=
  clearedMatrix_integral (CaterpillarRows.fullDim m) sourceRow column

/-- **Non-vacuity of `absMultNat`**: the caterpillar seed has natural-number
multiplicity one. -/
theorem fdAbsMultNat_caterpillar (m : ℕ) :
    fdAbsMultNat (CaterpillarRows.fullDim m) = 1 := by
  show (signedMult (CaterpillarRows.labelling m).presentation).num.natAbs = 1
  rw [Caterpillar.signedMult_caterpillar m]
  norm_num

/-- Hence `|det B'| = 1` is the integer `±1`, and the multiplicity is odd. -/
example (m : ℕ) : Odd (fdAbsMultNat (CaterpillarRows.fullDim m)) := by
  rw [fdAbsMultNat_caterpillar]
  exact odd_one

/-- **Non-vacuity of the oddness bridge**: the genus-`2m+2` caterpillar member
of the labelled fibre has natural-number multiplicity one, and
`HasOddMult` reads off it. -/
theorem oddMult_caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).oddMult = 1 :=
  fdAbsMultNat_caterpillar m

example (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).HasOddMult :=
  (hasOddMult_iff_odd_oddMult _).mpr (by
    rw [oddMult_caterpillarMember]
    exact odd_one)

/-- `g = 6`: the leaf column of `B'` at the first lollipop tip is a standard
basis vector, and the whole multiplicity is the natural number `1`. -/
example : fdAbsMultNat (CaterpillarRows.fullDim 2) = 1 := fdAbsMultNat_caterpillar 2

example (sourceRow : Fin (6 * 2 + 3)) :
    clearedMatrix (CaterpillarRows.labelling 2).presentation sourceRow
        ((CaterpillarRows.labelling 2).targetEdge.symm
          (leafEdge (LeafFibre.isLeafVertex_catTip 2))) =
      if sourceRow = leafRow (CaterpillarRows.fullDim 2)
        (LeafFibre.isLeafVertex_catTip 2) then 1 else 0 :=
  clearedMatrix_leafColumn (CaterpillarRows.fullDim 2)
    (LeafFibre.isLeafVertex_catTip 2) sourceRow

end Integrality

end DraismaVargas.Count
