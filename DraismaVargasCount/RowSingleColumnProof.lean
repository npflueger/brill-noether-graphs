module

public import DraismaVargasCount.SpineOffDiagonal

@[expose] public section

/-!
# What `RowSingleColumn` actually asks for: a census of surviving occurrences

**Source.**  Vargas, Part II (arXiv:2609.09109), the last paragraph of the
proof of `lm:combinatorial-structure-caterpillar-of-loops` ("each path edge
`h_i` contains a single edge of `G`", so the edge-length matrix `A_φ` is
diagonal), and `lm:bridge-and-loop`, whose proof is Draisma--Vargas Part I
(arXiv:1909.12924), `lemma-loop-bridge`.

`DraismaVargasCount.SpineOffDiagonal` reduces the diagonality of `A_φ` to the
single hypothesis

```
RowSingleColumn labelling sourceRow column :
  ∀ edge ∈ rowEdges labelling sourceRow, edge.1.1 = labelling.targetEdge column
```

and proves everything downstream of it.  This module does not prove that
hypothesis.  What it does is say **exactly what it is**, by eliminating
the target edge from the statement: over a full-dimensional presentation,
`RowSingleColumn` for a row is *equivalent* to a bound on the number of
surviving source occurrences the row displays --- **one**, except on the rows
passing above a leaf, where it is **two**.

That equivalence resolves an apparent tension.
`RowGeodesic.rowTargetInjective_of_genusZero` says the occurrences of a row have
pairwise distinct target images; `RowSingleColumn` says they all have the *same*
target image.  The two can hold together only if the row has a single
occurrence, and indeed:

* on a **leaf-avoiding** row both hold, and `RowSingleColumn` is precisely
  "`rowEdges` is a singleton" --- which is Part II's "each path edge `h_i`
  contains a single edge of `G`", verbatim;
* on a **loop row** `rowTargetInjective_of_genusZero` does *not* apply --- it
  needs `RowRamificationAtMostOne`, which fails exactly at the leaf core vertex
  `A_v` --- and `RowSingleColumn` is precisely "`rowEdges` is the two-element
  set `LeafFibre.leafSurvivors`", i.e. Part I's `h_l = ⟨A, e₁, C, e₂, A⟩`.

So `RowSingleColumn` is not weaker on loop rows than on spine rows: it is a
length-two statement there and a length-one statement elsewhere.  The diagonality
of `A_φ` it serves is part of the description of the members over the caterpillar
of loops behind the base count (`CaterpillarAllMembers`, step 1 of
`DraismaVargasCount.Assembly`).

## What is proved

* §1 `rowSingleColumn_iff_rowEdges_eq_rowFibre` --- the elimination: a row lies
  above one column exactly when its displayed occurrences are its fibre above
  that column.  `column_eq_of_rowSingleColumn` --- the column is unique.
* §2 `exists_rowSingleColumn_of_card_eq_one`,
  `card_rowEdges_eq_one_of_rowSingleColumn_of_not_passesAboveLeaf` --- on a
  leaf-avoiding row, `RowSingleColumn` **is** `rowEdges.card = 1`, in both
  directions.  The forward direction is where
  `SharpRowDenominator.rowFibre_eq_singleton_of_not_passesAboveLeaf` enters, and
  it is the only place it can.
* §3 `leafSurvivors_subset_rowEdges`, `two_le_card_rowEdges_leafRow`,
  `targetEdge_eq_leafEdge_of_rowSingleColumn_leafRow`,
  `rowSingleColumn_leafRow_iff` --- on a leaf row, `RowSingleColumn` **is**
  `rowEdges.card = 2`, the column is forced to be the leaf edge, and the lower
  bound `2 ≤ rowEdges.card` is unconditional.  `not_rowTargetInjective_leafRow`
  --- `RowWalk.RowTargetInjective` is **false** on a leaf row, so the two
  predicates of the tension above genuinely do not both hold there.
* §4 `exists_rowSingleColumn_iff` --- the two halves as one biconditional, and
  `exists_rowSingleColumn_of_card_le`: `RowSingleColumn` for a row follows from a
  pure **upper** bound on its occurrence count, the matching lower bounds being
  free.
* §5 `rowEdges_eq_toFinset_orderedRow`, `card_rowEdges_eq_length_orderedRow` ---
  that count is the length of `Count.RowWalk.orderedRow`, so the upper bound can
  be proved on the ordered walk.
* §6 the member-level forms: `exists_perm_rowSingleColumn_iff` and
  `exists_perm_member_matrix_diagonal_of_card`, which is
  `SpineOffDiagonal.exists_perm_member_matrix_diagonal` with its hypothesis
  replaced by the census.  `card_rowEdges_core_loop_iff` and
  `two_le_card_rowEdges_core_loop` specialise to a self-loop slot of the core.

## What is not proved here (every hypothesis, explicitly)

* **`RowSingleColumn` itself is not proved here, for any row.**  Everything
  below is an equivalent restatement of it.  What it needs is the pair of
  *upper* bounds `(rowEdges fd.labelling sourceRow).card ≤ 1` on a
  leaf-avoiding row and `≤ 2` on a leaf row; §4's
  `exists_rowSingleColumn_of_card_le` is stated so that exactly those two are
  its hypotheses.  On the loop rows it is proved downstream
  (`PassOnceLollipopWitness.exists_rowSingleColumn_core_loop`); the diagonality
  of `A_φ` at the open classes of odd multiplicity over the caterpillar is
  `TrivalentFibreUnique.diagonal`.
* **The hairpin does not settle the loop rows.**
  `LollipopDivalentWitness.loopReturnsSameDirection` constrains only the two
  occurrences *incident to the branch vertex* --- the first and last entries of
  the ordered row.  It says nothing about the interior ones, so it does not give
  `RowSingleColumn` on a loop row: that needs the ordered row to have length
  two, which is the clause `h_l = ⟨A, e₁, C, e₂, A⟩` of `lm:bridge-and-loop`;
  `LollipopLeafRow` proves only that the row is `LeafFibre.leafRow` of a leaf.
  Part I gets that clause from the **pass-once** condition (`lemma-pass-once`, a
  column-dependence argument `a₂ = a₁ + a₃` against full rank).  The modules
  imported here have pass-once only in the leaf-avoiding form
  (`SharpRowDenominator.rowTargetInjective_of_not_passesAboveLeaf`), which does
  not apply to a row that passes above a leaf; the lollipop case is
  `DraismaVargasCount.PassOnceLollipop`, downstream.
* **No spine path, no edge budget, no genus, no degree, no request.**  Nothing
  below mentions `catCore`, `ballotDatum`, `Open`, `HasOddMult`,
  `GeometricFibre` or `openOddCount`; §6 is stated for an arbitrary
  `FibreMember core y degree` over an arbitrary core, which is the
  quantification the proof of
  `lm:combinatorial-structure-caterpillar-of-loops` needs.
* Nothing here identifies the bijection `σ` with any geometrically named map.
-/

namespace DraismaVargas.Count.RowSingleColumnProof

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.LeafFibre
open DraismaVargas.Count.EdgeDenominator
open DraismaVargas.Count.RowWalk
open DraismaVargas.Count.SpineOffDiagonal

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ## 1.  Eliminating the target edge -/

omit [Fintype coordinate] in
/-- **`RowSingleColumn` says the row is its own fibre above one column.**  This
is the whole of the predicate, with the target edge eliminated. -/
theorem rowSingleColumn_iff_rowEdges_eq_rowFibre
    (labelling : StableLengthMatrixLabelling data coordinate) (sourceRow column : coordinate) :
    RowSingleColumn labelling sourceRow column ↔
      rowEdges labelling sourceRow =
        rowFibre labelling sourceRow (labelling.targetEdge column) := by
  constructor
  · intro hSingle
    refine Finset.Subset.antisymm (fun edge hEdge ↦ ?_)
      (rowFibre_subset_rowEdges labelling sourceRow _)
    exact (mem_rowFibre_iff labelling sourceRow _ edge).mpr ⟨hEdge, hSingle edge hEdge⟩
  · intro hEq edge hEdge
    rw [hEq] at hEdge
    exact ((mem_rowFibre_iff labelling sourceRow _ edge).mp hEdge).2

omit [Fintype coordinate] in
/-- **The column of a row supported in one column is unique.**  A stable row is
never empty (`SharpRowDenominator.rowEdges_nonempty`). -/
theorem column_eq_of_rowSingleColumn
    {labelling : StableLengthMatrixLabelling data coordinate}
    {sourceRow column column' : coordinate}
    (hSingle : RowSingleColumn labelling sourceRow column)
    (hSingle' : RowSingleColumn labelling sourceRow column') : column = column' := by
  obtain ⟨edge, hEdge⟩ := SharpRowDenominator.rowEdges_nonempty labelling sourceRow
  exact labelling.targetEdge.injective ((hSingle edge hEdge).symm.trans (hSingle' edge hEdge))

/-! ## 2.  A row of one occurrence, and the leaf-avoiding converse -/

omit [Fintype coordinate] in
/-- **One displayed occurrence gives `RowSingleColumn`**, with no hypothesis on
the target, the presentation, or the leaves. -/
theorem exists_rowSingleColumn_of_card_eq_one
    (labelling : StableLengthMatrixLabelling data coordinate) {sourceRow : coordinate}
    (hCard : (rowEdges labelling sourceRow).card = 1) :
    ∃ column, RowSingleColumn labelling sourceRow column := by
  obtain ⟨edge, hEq⟩ := Finset.card_eq_one.mp hCard
  refine ⟨labelling.targetEdge.symm edge.1.1, fun other hOther ↦ ?_⟩
  rw [hEq, Finset.mem_singleton] at hOther
  rw [hOther, Equiv.apply_symm_apply]

/-- **On a leaf-avoiding row, `RowSingleColumn` forces a single occurrence.**
This is the tension of the introduction, resolved: the row's occurrences have
pairwise distinct target images
(`SharpRowDenominator.rowFibre_eq_singleton_of_not_passesAboveLeaf`, itself
`RowGeodesic.rowTargetInjective_of_genusZero`), and `RowSingleColumn` says they
all have the same one. -/
theorem card_rowEdges_eq_one_of_rowSingleColumn_of_not_passesAboveLeaf
    (fd : FullDimensionalSourcePresentation data coordinate) {sourceRow column : coordinate}
    (hAvoid : ¬ PassesAboveLeaf fd.labelling sourceRow)
    (hSingle : RowSingleColumn fd.labelling sourceRow column) :
    (rowEdges fd.labelling sourceRow).card = 1 := by
  obtain ⟨edge, hEdge⟩ := SharpRowDenominator.rowEdges_nonempty fd.labelling sourceRow
  have hFibre := SharpRowDenominator.rowFibre_eq_singleton_of_not_passesAboveLeaf fd hAvoid hEdge
  have hEq := (rowSingleColumn_iff_rowEdges_eq_rowFibre fd.labelling sourceRow column).mp hSingle
  have hTarget : fd.labelling.targetEdge column = edge.1.1 := (hSingle edge hEdge).symm
  rw [hEq, hTarget, hFibre, Finset.card_singleton]

/-! ## 3.  The leaf rows: `RowSingleColumn` is a length-two statement -/

section LeafRow

variable (fd : FullDimensionalSourcePresentation data coordinate) {leaf : target.V}

/-- Both surviving occurrences above the leaf edge are displayed on `h(v)`. -/
theorem leafSurvivors_subset_rowEdges (hLeaf : IsLeafVertex target leaf) :
    leafSurvivors (data := data) hLeaf ⊆ rowEdges fd.labelling (leafRow fd hLeaf) := by
  intro edge hMem
  obtain ⟨hSurvives, _⟩ := (mem_leafSurvivors hLeaf).mp hMem
  exact (mem_rowEdges fd.labelling _ edge).mpr
    ⟨hSurvives, row_eq_leafRow fd hLeaf hMem hSurvives⟩

/-- **A leaf row displays at least two occurrences**, unconditionally.  So on a
leaf row `RowSingleColumn` amounts to the *upper* bound. -/
theorem two_le_card_rowEdges_leafRow (hLeaf : IsLeafVertex target leaf) :
    2 ≤ (rowEdges fd.labelling (leafRow fd hLeaf)).card := by
  have hCard := leafSurvivors_card (data := data) fd hLeaf
  have hLe := Finset.card_le_card (leafSurvivors_subset_rowEdges fd hLeaf)
  omega

/-- **The column of a leaf row can only be its leaf edge.** -/
theorem targetEdge_eq_leafEdge_of_rowSingleColumn_leafRow (hLeaf : IsLeafVertex target leaf)
    {column : coordinate}
    (hSingle : RowSingleColumn fd.labelling (leafRow fd hLeaf) column) :
    column = fd.labelling.targetEdge.symm (leafEdge hLeaf) := by
  have hMem : leafSurvivor fd hLeaf ∈ rowEdges fd.labelling (leafRow fd hLeaf) :=
    leafSurvivors_subset_rowEdges fd hLeaf (leafSurvivor_mem fd hLeaf)
  have hTarget := hSingle _ hMem
  rw [(leafSurvivor_spec fd hLeaf).1] at hTarget
  rw [hTarget, Equiv.symm_apply_apply]

/-- **On a leaf row, `RowSingleColumn` *is* "exactly two occurrences".**  Its
content is Part I's `h_l = ⟨A, e₁, C, e₂, A⟩`, not the hairpin. -/
theorem rowSingleColumn_leafRow_iff (hLeaf : IsLeafVertex target leaf) :
    RowSingleColumn fd.labelling (leafRow fd hLeaf)
        (fd.labelling.targetEdge.symm (leafEdge hLeaf)) ↔
      (rowEdges fd.labelling (leafRow fd hLeaf)).card = 2 := by
  rw [rowSingleColumn_iff_rowEdges_eq_rowFibre, Equiv.apply_symm_apply,
    rowFibre_leafEdge fd hLeaf, ite_eq_left rfl]
  constructor
  · intro hEq
    rw [hEq]
    exact leafSurvivors_card (data := data) fd hLeaf
  · intro hCard
    refine (Finset.eq_of_subset_of_card_le (leafSurvivors_subset_rowEdges fd hLeaf) ?_).symm
    rw [hCard, leafSurvivors_card (data := data) fd hLeaf]

/-- **`RowTargetInjective` fails on every leaf row.**  The
two surviving occurrences above the leaf edge are distinct and have the same
target image.  This is why
`RowGeodesic.rowTargetInjective_of_genusZero` --- whose hypothesis
`RowRamificationAtMostOne` fails at the leaf core vertex --- cannot be combined
with `RowSingleColumn` on such a row to force a single occurrence, and why the
leaf rows have their own, length-two, form of the single-column statement. -/
theorem not_rowTargetInjective_leafRow (hLeaf : IsLeafVertex target leaf) :
    ¬ RowTargetInjective data (fd.labelling.row.symm (leafRow fd hLeaf)) := by
  intro hInj
  obtain ⟨first, hFirst, second, hSecond, hNe⟩ := Finset.one_lt_card.mp
    (by rw [leafSurvivors_card (data := data) fd hLeaf]; norm_num :
      1 < (leafSurvivors (data := data) hLeaf).card)
  refine hNe (hInj first second ?_ ?_ ?_)
  · exact (mem_rowEdges_iff_onRow fd.labelling _ first).mp
      (leafSurvivors_subset_rowEdges fd hLeaf hFirst)
  · exact (mem_rowEdges_iff_onRow fd.labelling _ second).mp
      (leafSurvivors_subset_rowEdges fd hLeaf hSecond)
  · rw [((mem_leafSurvivors hLeaf).mp hFirst).2, ((mem_leafSurvivors hLeaf).mp hSecond).2]

end LeafRow

/-! ## 4.  The census, and `RowSingleColumn` from an upper bound -/

/-- **`RowSingleColumn` for one row, as a census of its surviving occurrences.**  A stable row
lies above a single target edge exactly when it displays one occurrence, or two
when it passes above a leaf.  No other possibility is consistent with it. -/
theorem exists_rowSingleColumn_iff
    (fd : FullDimensionalSourcePresentation data coordinate) (sourceRow : coordinate) :
    (∃ column, RowSingleColumn fd.labelling sourceRow column) ↔
      ((¬ PassesAboveLeaf fd.labelling sourceRow ∧
          (rowEdges fd.labelling sourceRow).card = 1) ∨
        (PassesAboveLeaf fd.labelling sourceRow ∧
          (rowEdges fd.labelling sourceRow).card = 2)) := by
  constructor
  · rintro ⟨column, hSingle⟩
    by_cases hPasses : PassesAboveLeaf fd.labelling sourceRow
    · refine Or.inr ⟨hPasses, ?_⟩
      obtain ⟨vertex, hLeaf, hRow⟩ := exists_eq_leafRow_of_passesAboveLeaf fd hPasses
      subst hRow
      rw [← rowSingleColumn_leafRow_iff fd hLeaf,
        ← targetEdge_eq_leafEdge_of_rowSingleColumn_leafRow fd hLeaf hSingle]
      exact hSingle
    · exact Or.inl ⟨hPasses,
        card_rowEdges_eq_one_of_rowSingleColumn_of_not_passesAboveLeaf fd hPasses hSingle⟩
  · rintro (⟨-, hCard⟩ | ⟨hPasses, hCard⟩)
    · exact exists_rowSingleColumn_of_card_eq_one fd.labelling hCard
    · obtain ⟨vertex, hLeaf, hRow⟩ := exists_eq_leafRow_of_passesAboveLeaf fd hPasses
      subst hRow
      exact ⟨_, (rowSingleColumn_leafRow_iff fd hLeaf).mpr hCard⟩

/-- **On one row, `RowSingleColumn` follows from a pure upper bound.**  The matching lower
bounds are already proved: `SharpRowDenominator.rowEdges_nonempty` on any row
and `two_le_card_rowEdges_leafRow` on a leaf row. -/
theorem exists_rowSingleColumn_of_card_le
    (fd : FullDimensionalSourcePresentation data coordinate) (sourceRow : coordinate)
    (hAvoid : ¬ PassesAboveLeaf fd.labelling sourceRow →
      (rowEdges fd.labelling sourceRow).card ≤ 1)
    (hLeaf : PassesAboveLeaf fd.labelling sourceRow →
      (rowEdges fd.labelling sourceRow).card ≤ 2) :
    ∃ column, RowSingleColumn fd.labelling sourceRow column := by
  refine (exists_rowSingleColumn_iff fd sourceRow).mpr ?_
  by_cases hPasses : PassesAboveLeaf fd.labelling sourceRow
  · refine Or.inr ⟨hPasses, ?_⟩
    obtain ⟨vertex, hLeafVertex, hRow⟩ := exists_eq_leafRow_of_passesAboveLeaf fd hPasses
    have hUpper := hLeaf hPasses
    have hLower := two_le_card_rowEdges_leafRow fd hLeafVertex
    rw [← hRow] at hLower
    omega
  · refine Or.inl ⟨hPasses, ?_⟩
    have hUpper := hAvoid hPasses
    have hLower := Finset.card_pos.mpr
      (SharpRowDenominator.rowEdges_nonempty fd.labelling sourceRow)
    omega

/-! ## 5.  The count is the length of the ordered row -/

/-- The displayed occurrences of a stable row are the entries of its ordered
walk (`Count.RowWalk.orderedRow`). -/
theorem rowEdges_eq_toFinset_orderedRow
    (fd : FullDimensionalSourcePresentation data coordinate) (path : StablePath data) :
    rowEdges fd.labelling (fd.labelling.row path) = (orderedRow fd.pathEnds path).toFinset := by
  classical
  ext edge
  rw [List.mem_toFinset, mem_orderedRow_iff, mem_rowEdges_iff_onRow, Equiv.symm_apply_apply]

/-- **The occurrence count of a row is the length of its ordered walk**, the
ordered walk being duplicate-free.  So the upper bound of §4 is a bound on the
walk length: `1` off the leaves, `2` on a leaf row. -/
theorem card_rowEdges_eq_length_orderedRow
    (fd : FullDimensionalSourcePresentation data coordinate) (path : StablePath data) :
    (rowEdges fd.labelling (fd.labelling.row path)).card = (orderedRow fd.pathEnds path).length := by
  rw [rowEdges_eq_toFinset_orderedRow fd path,
    List.toFinset_card_of_nodup (orderedRow_nodup fd.pathEnds path)]

/-! ## 6.  At an arbitrary member of the fibre -/

section Member

open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
  (member : FibreMember core y degree)

/-- **The single-column hypothesis, at an arbitrary member, as a census.**  This is the
statement `SpineOffDiagonal.exists_perm_member_matrix_diagonal` consumes, with
the target edges eliminated. -/
theorem exists_perm_rowSingleColumn_iff :
    (∃ σ : Fin p → Fin p, ∀ sourceRow,
        RowSingleColumn member.fullDim.labelling sourceRow (σ sourceRow)) ↔
      ∀ sourceRow : Fin p,
        ((¬ PassesAboveLeaf member.fullDim.labelling sourceRow ∧
            (rowEdges member.fullDim.labelling sourceRow).card = 1) ∨
          (PassesAboveLeaf member.fullDim.labelling sourceRow ∧
            (rowEdges member.fullDim.labelling sourceRow).card = 2)) := by
  constructor
  · rintro ⟨σ, hσ⟩ sourceRow
    exact (exists_rowSingleColumn_iff member.fullDim sourceRow).mp ⟨σ sourceRow, hσ sourceRow⟩
  · intro hCensus
    choose σ hσ using fun sourceRow ↦
      (exists_rowSingleColumn_iff member.fullDim sourceRow).mpr (hCensus sourceRow)
    exact ⟨σ, hσ⟩

/-- **`A_φ` is a monomial matrix at an arbitrary member as soon as the census
holds.**  `SpineOffDiagonal.exists_perm_member_matrix_diagonal` with its
hypothesis replaced by the occurrence count. -/
theorem exists_perm_member_matrix_diagonal_of_card
    (hCensus : ∀ sourceRow : Fin p,
      ((¬ PassesAboveLeaf member.fullDim.labelling sourceRow ∧
          (rowEdges member.fullDim.labelling sourceRow).card = 1) ∨
        (PassesAboveLeaf member.fullDim.labelling sourceRow ∧
          (rowEdges member.fullDim.labelling sourceRow).card = 2))) :
    ∃ e : Equiv.Perm (Fin p),
      (∀ sourceRow column : Fin p, column ≠ e sourceRow →
        member.matrix sourceRow column = 0) ∧
      (∀ sourceRow : Fin p, member.matrix sourceRow (e sourceRow) ≠ 0) := by
  obtain ⟨σ, hσ⟩ := (exists_perm_rowSingleColumn_iff member).mpr hCensus
  exact exists_perm_member_matrix_diagonal member hσ

/-- **A loop row of the core displays at least two occurrences.**  The row of a
self-loop slot is the leaf row of a leaf (`LollipopLeafRow.leafRow_loopLeaf`),
and both survivors above that leaf edge sit on it. -/
theorem two_le_card_rowEdges_core_loop {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    2 ≤ (rowEdges member.fullDim.labelling
      (member.fullDim.labelling.row (member.ident.row.symm slot))).card := by
  have hLower := two_le_card_rowEdges_leafRow member.fullDim
    (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)
  rwa [LollipopLeafRow.leafRow_loopLeaf member hLoop] at hLower

/-- **On a loop row of the core, `RowSingleColumn` is exactly "the row has
length two".**  This is the clause `h_l = ⟨A, e₁, C, e₂, A⟩` of
`lm:bridge-and-loop`; the hairpin
`LollipopDivalentWitness.loopReturnsSameDirection` constrains only the two ends
of the row and does not give it by itself. -/
theorem card_rowEdges_core_loop_iff {slot : Fin p}
    (hLoop : core.tail slot = core.head slot) :
    (∃ column, RowSingleColumn member.fullDim.labelling
        (member.fullDim.labelling.row (member.ident.row.symm slot)) column) ↔
      (rowEdges member.fullDim.labelling
        (member.fullDim.labelling.row (member.ident.row.symm slot))).card = 2 := by
  have hLeafRow := LollipopLeafRow.leafRow_loopLeaf member hLoop
  constructor
  · intro hExists
    rw [← hLeafRow] at hExists ⊢
    obtain ⟨column, hSingle⟩ := hExists
    rw [← rowSingleColumn_leafRow_iff member.fullDim
      (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop),
      ← targetEdge_eq_leafEdge_of_rowSingleColumn_leafRow member.fullDim
        (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop) hSingle]
    exact hSingle
  · intro hCard
    rw [← hLeafRow] at hCard ⊢
    exact ⟨_, (rowSingleColumn_leafRow_iff member.fullDim
      (LollipopLeafRow.loopLeaf_isLeafVertex member hLoop)).mpr hCard⟩

end Member

end DraismaVargas.Count.RowSingleColumnProof
