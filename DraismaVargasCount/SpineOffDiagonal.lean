module

public import DraismaVargasCount.SharpRowDenominator
public import DraismaVargasCount.LollipopLeafRow

@[expose] public section

/-!
# `A_φ` is a monomial matrix: the off-diagonal half of diagonality

**Source.**  Vargas, Part II (arXiv:2609.09109), the last paragraph of the proof of
`lm:combinatorial-structure-caterpillar-of-loops`: each path edge `h_i`
"contains a single edge of `G`", so the edge-length matrix `A_φ` is diagonal.
This module splits that diagonality statement into an on-diagonal half (every
stable row lies above a single target edge) and an off-diagonal half (distinct
stable rows meet distinct columns), and shows that they are one statement.
`MemberColumnTwist` uses the result (`exists_perm_member_matrix_diagonal`) to
make members diagonal by re-indexing their columns, in the classification of
the members over the caterpillar of loops behind the base count (step 1 of
`DraismaVargasCount/Assembly.lean`).

## The structure of the statement

* `SharpRowDenominator.rowFibre_eq_singleton_of_not_passesAboveLeaf` says that
  a leaf-avoiding row meets each target edge it meets *exactly once*.  It says
  nothing about how many target edges the row meets, so it is **not** the
  statement "`h_i` contains a single edge of `G`".  On a loop row it is in fact
  unavailable: a loop row passes above a leaf
  (`LollipopLeafRow.not_rowAvoidsLeaves_of_loopRow`), and its two source
  occurrences do lie above one target edge, so its fibre there has two
  elements.
* A statement indexed by the request slots of a `Spec` is not this statement
  either.  Its columns are the **source** request slots `Fin p` of a `Spec`,
  reached through `member.ident.row`, while the columns here are the **target**
  edges of `T`, reached through `fullDim.labelling.targetEdge`; the two index
  sets are both `Fin p` only by a coincidence of the labelling.  And such a
  statement cannot be instantiated in the caterpillar fibre at all:
  `Spec.core_loopless` forbids a core with a self-loop, and `catCore m` has
  `2m+2` of them — `catCore_ne_spec_core` below proves exactly this.
* The two halves are **not independent**.  `A_φ` is square and nonsingular
  (`FullDimensionalSourcePresentation.det_ne_zero`), and for a square
  nonsingular matrix "the row supports are pairwise disjoint" and "every row
  support is a singleton" are *equivalent*, each implying that the resulting
  column map is a bijection.  Proving either one proves the other, and each of
  them is exactly "`A_φ` is diagonal up to the labelling of columns".

So diagonality is exactly **one** obligation, not two: the hypothesis
`RowSingleColumn` below.  What this module contributes is everything *except*
that obligation: the linear algebra, the dictionary between matrix entries and
row geometry, and the two implications joining the halves.

## What is proved

* §0 `catCore_ne_spec_core` — no `Spec` has the caterpillar core, so the
  `Spec`-slot dictionary is vacuous over this fibre.
* §1, abstract and over any commutative ring: `rowSupport`,
  `rowSupport_nonempty` (nonsingular ⟹ no zero row),
  `column_surjective_of_det_ne_zero` and `column_bijective_of_det_ne_zero` (if
  every row is supported in a single column `σ r`, then `σ` is a bijection —
  otherwise a column is identically zero), `rowSupport_card_eq_one_of_disjoint`
  and `exists_column_perm_of_disjoint` (conversely, pairwise disjoint row
  supports on a nonsingular square matrix are forced to be singletons, and the
  resulting map is a permutation).
* §2 `Meets`, `matrix_ne_zero_iff_meets` — the dictionary: the entry of `A_φ`
  at row `i`, column `c` is nonzero exactly when some surviving occurrence of
  the stable row `i` lies above the target edge `c`.  All the terms of
  `LeafFibre.matrix_eq_sum_fibre` are strictly positive, so no cancellation can
  hide a meeting.
* §3 `RowSingleColumn` (the obligation, as a named predicate),
  `matrix_eq_zero_of_rowSingleColumn`, `column_bijective_of_rowSingleColumn`,
  `meets_row_unique_of_rowSingleColumn` — **the off-diagonal half, derived from
  the on-diagonal half**; and `rowSingleColumn_of_meets_row_unique` — the
  converse, so the two halves are one obligation.
* §4 `member_matrix_eq_zero_of_ne`, `member_column_bijective`,
  `exists_perm_member_matrix_diagonal` — the same at an arbitrary
  `FibreMember`, which is the quantification the classification of the
  caterpillar fibre needs: `A_φ` is a
  monomial matrix, i.e. `∃ σ : Equiv.Perm (Fin p)` with every off-`σ` entry
  zero and every on-`σ` entry nonzero.

## Scope

* **`RowSingleColumn` itself is not proved here.**  Every statement of §3
  and §4 carries it as a hypothesis (in §4, as `hSingle`).  It is exactly the
  geometric content of diagonality, and by §3's converse it is also exactly the
  off-diagonal statement; nothing in this module reduces its cost.
  `RowSingleColumnProof` says exactly what it asks for.
* Nothing here is about the caterpillar.  No statement mentions `catCore`,
  `ballotDatum`, `Open`, `HasOddMult`, the genus, the degree or the request:
  §4 is stated for an arbitrary `FibreMember core y degree` over an arbitrary
  core.  That is deliberate: the classification of the caterpillar fibre
  quantifies over an arbitrary member.
* No spine path is constructed and no edge budget is proved; for those see
  `DraismaVargasCount.SpinePath`.
* The bijection `σ` of §4 is not identified with any geometrically named map.
  In particular nothing here says `σ` carries a spine row to a spine edge of
  `T`, or a loop row to a leaf edge; that identification needs the structure
  of the lollipops (each loop lies over a leaf edge of `T`, and the `g`
  lollipops have `2g` distinct image edges) and is not attempted.
-/

namespace DraismaVargas.Count.SpineOffDiagonal

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.LeafFibre
open DraismaVargas.Count.EdgeDenominator

/-! ## 0.  Why the `Spec`-slot dictionary is not this statement -/

section SpecSlots

open DraismaVargas.Count.FibreCaterpillar
open Utilities.Certificate.SubdivisionGraph

/-- **No `Spec` has the caterpillar of loops as its core.**  `Spec.core_loopless`
forbids a slot whose two ends coincide, and `catCore m` has `2m+2` such slots
(`LollipopLeafRow.card_catCore_loopSlots`).

The consequence: a member-level statement about a
`member : FibreMember spec.core …` with `spec : Spec n p` **cannot be
instantiated anywhere in the caterpillar fibre**.  That is independent of the
fact, recorded above, that the columns of such a statement are source request
slots rather than target edges. -/
theorem catCore_ne_spec_core (m : ℕ) (spec : Spec (4 * m + 2) (6 * m + 3)) :
    spec.core ≠ catCore m := by
  intro h
  have hpos : 0 < Fintype.card {slot : Fin (6 * m + 3) //
      (catCore m).tail slot = (catCore m).head slot} := by
    rw [LollipopLeafRow.card_catCore_loopSlots m]
    omega
  obtain ⟨slot, hslot⟩ := Fintype.card_pos_iff.mp hpos
  exact spec.core_loopless slot (by rw [h]; exact hslot)

end SpecSlots

/-! ## 1.  Square nonsingular matrices with thin rows -/

section LinearAlgebra

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set of columns in which a matrix row is nonzero. -/
noncomputable def rowSupport (M : Matrix ι ι R) (r : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun c ↦ M r c ≠ 0

omit [DecidableEq ι] in
theorem mem_rowSupport {M : Matrix ι ι R} {r c : ι} :
    c ∈ rowSupport M r ↔ M r c ≠ 0 := by
  classical
  simp [rowSupport]

/-- A nonsingular matrix has no zero row. -/
theorem rowSupport_nonempty {M : Matrix ι ι R} (hDet : M.det ≠ 0) (r : ι) :
    (rowSupport M r).Nonempty := by
  classical
  by_contra hEmpty
  rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
  refine hDet (Matrix.det_eq_zero_of_row_eq_zero r fun c ↦ ?_)
  by_contra hne
  have hmem : c ∈ rowSupport M r := mem_rowSupport.mpr hne
  rw [hEmpty] at hmem
  simp at hmem

/-- **If every row of a nonsingular square matrix is supported in the single
column `σ r`, then `σ` is onto.**  Otherwise a column missed by `σ` is
identically zero. -/
theorem column_surjective_of_det_ne_zero {M : Matrix ι ι R} (hDet : M.det ≠ 0)
    {σ : ι → ι} (hSupport : ∀ r c, c ≠ σ r → M r c = 0) :
    Function.Surjective σ := by
  intro c
  by_contra hc
  exact hDet (Matrix.det_eq_zero_of_column_eq_zero c fun r ↦ hSupport r c fun h ↦ hc ⟨r, h.symm⟩)

/-- The same map is a bijection, the index type being finite. -/
theorem column_bijective_of_det_ne_zero {M : Matrix ι ι R} (hDet : M.det ≠ 0)
    {σ : ι → ι} (hSupport : ∀ r c, c ≠ σ r → M r c = 0) :
    Function.Bijective σ :=
  (Finite.surjective_iff_bijective).mp (column_surjective_of_det_ne_zero hDet hSupport)

/-- In particular the column map is injective: **distinct rows meet distinct
columns.** -/
theorem column_injective_of_det_ne_zero {M : Matrix ι ι R} (hDet : M.det ≠ 0)
    {σ : ι → ι} (hSupport : ∀ r c, c ≠ σ r → M r c = 0) :
    Function.Injective σ :=
  (column_bijective_of_det_ne_zero hDet hSupport).1

/-- The on-diagonal entry of such a matrix is nonzero: the row is not zero and
every other entry of it is. -/
theorem entry_ne_zero_of_support {M : Matrix ι ι R} (hDet : M.det ≠ 0)
    {σ : ι → ι} (hSupport : ∀ r c, c ≠ σ r → M r c = 0) (r : ι) :
    M r (σ r) ≠ 0 := by
  obtain ⟨c, hc⟩ := rowSupport_nonempty hDet r
  have hcσ : c = σ r := by
    by_contra hne
    exact mem_rowSupport.mp hc (hSupport r c hne)
  rw [← hcσ]
  exact mem_rowSupport.mp hc

/-- **The converse direction.**  On a square nonsingular matrix, pairwise
disjoint row supports are forced to be singletons: there are as many rows as
columns, each support is nonempty, and disjoint nonempty sets cannot fit
otherwise. -/
theorem rowSupport_card_eq_one_of_disjoint {M : Matrix ι ι R} (hDet : M.det ≠ 0)
    (hDisj : ∀ r r', r ≠ r' → Disjoint (rowSupport M r) (rowSupport M r')) (r : ι) :
    (rowSupport M r).card = 1 := by
  classical
  have hPos : ∀ s ∈ (Finset.univ : Finset ι), 1 ≤ (rowSupport M s).card := fun s _ ↦
    Finset.card_pos.mpr (rowSupport_nonempty hDet s)
  have hBiUnion : ((Finset.univ : Finset ι).biUnion (rowSupport M)).card =
      ∑ s : ι, (rowSupport M s).card :=
    Finset.card_biUnion fun x _ y _ hxy ↦ hDisj x y hxy
  have hLe : ∑ s : ι, (rowSupport M s).card ≤ Fintype.card ι := by
    rw [← hBiUnion, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hConst : ∑ _s : ι, 1 = Fintype.card ι := by
    simp [Finset.card_univ]
  have hEq : ∑ _s : ι, 1 = ∑ s : ι, (rowSupport M s).card :=
    le_antisymm (Finset.sum_le_sum hPos) (by rw [hConst]; exact hLe)
  exact ((Finset.sum_eq_sum_iff_of_le hPos).mp hEq r (Finset.mem_univ r)).symm

/-- Pairwise disjoint row supports, packaged as a permutation of the columns
together with the two-sided description of the nonzero entries.  This is "`M`
is a monomial matrix" in the form the count consumes. -/
theorem exists_column_perm_of_disjoint {M : Matrix ι ι R} (hDet : M.det ≠ 0)
    (hDisj : ∀ r r', r ≠ r' → Disjoint (rowSupport M r) (rowSupport M r')) :
    ∃ σ : ι → ι, Function.Bijective σ ∧ ∀ r c, M r c ≠ 0 ↔ c = σ r := by
  classical
  have hSingleton : ∀ r, ∃ c, rowSupport M r = {c} := fun r ↦
    Finset.card_eq_one.mp (rowSupport_card_eq_one_of_disjoint hDet hDisj r)
  choose σ hσ using hSingleton
  have hIff : ∀ r c, M r c ≠ 0 ↔ c = σ r := by
    intro r c
    rw [← mem_rowSupport, hσ r, Finset.mem_singleton]
  refine ⟨σ, column_bijective_of_det_ne_zero hDet fun r c hc ↦ ?_, hIff⟩
  by_contra hne
  exact hc ((hIff r c).mp hne)

/-- The direction used to see that the two halves of diagonality are one statement:
a single-column support family has pairwise disjoint supports. -/
theorem disjoint_rowSupport_of_support {M : Matrix ι ι R} (hDet : M.det ≠ 0)
    {σ : ι → ι} (hSupport : ∀ r c, c ≠ σ r → M r c = 0) (r r' : ι) (hne : r ≠ r') :
    Disjoint (rowSupport M r) (rowSupport M r') := by
  classical
  rw [Finset.disjoint_left]
  intro c hc hc'
  have h1 : c = σ r := by
    by_contra hcc
    exact mem_rowSupport.mp hc (hSupport r c hcc)
  have h2 : c = σ r' := by
    by_contra hcc
    exact mem_rowSupport.mp hc' (hSupport r' c hcc)
  exact hne (column_injective_of_det_ne_zero hDet hSupport (h1 ▸ h2 ▸ rfl))

end LinearAlgebra

/-! ## 2.  The dictionary: a nonzero entry is a meeting -/

section Dictionary

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Row `sourceRow` meets column `column`**: some surviving occurrence of the
stable row lies above the target edge that `column` labels. -/
def Meets (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow column : coordinate) : Prop :=
  ∃ edge ∈ rowEdges labelling sourceRow, edge.1.1 = labelling.targetEdge column

omit [Fintype coordinate] in
theorem meets_iff_rowFibre_nonempty (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow column : coordinate) :
    Meets labelling sourceRow column ↔
      (rowFibre labelling sourceRow (labelling.targetEdge column)).Nonempty := by
  constructor
  · rintro ⟨edge, hEdge, hTarget⟩
    exact ⟨edge, (mem_rowFibre_iff labelling sourceRow _ edge).mpr ⟨hEdge, hTarget⟩⟩
  · rintro ⟨edge, hEdge⟩
    obtain ⟨hRow, hTarget⟩ := (mem_rowFibre_iff labelling sourceRow _ edge).mp hEdge
    exact ⟨edge, hRow, hTarget⟩

omit [Fintype coordinate] in
/-- **The entry of `A_φ` at `(sourceRow, column)` is nonzero exactly when the
row meets the column.**  `LeafFibre.matrix_eq_sum_fibre` presents the entry as
`∑ 1 / m(e)` over the fibre, and every term is strictly positive, so no
cancellation can hide a meeting. -/
theorem matrix_ne_zero_iff_meets (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow column : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix labelling.presentation sourceRow column ≠ 0 ↔
      Meets labelling sourceRow column := by
  classical
  have hEntry := matrix_eq_sum_fibre labelling sourceRow (labelling.targetEdge column)
  rw [Equiv.symm_apply_apply] at hEntry
  rw [hEntry, meets_iff_rowFibre_nonempty]
  constructor
  · intro hne
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    exact hne (by rw [hEmpty]; simp)
  · intro hNonempty
    refine ne_of_gt (Finset.sum_pos (fun edge _ ↦ ?_) hNonempty)
    have hPos : (0 : ℚ) < (data.sourceEdgeIndex edge : ℚ) := by
      exact_mod_cast sourceEdgeIndex_pos data edge
    exact div_pos one_pos hPos

end Dictionary

/-! ## 3.  The obligation, and the two implications joining its halves -/

section S4

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The diagonality obligation, as a named predicate.**  Every surviving occurrence of
the stable row `sourceRow` lies above one and the same target edge, the one
labelled by `column`.  For a spine row of the caterpillar this is the paper's
"`h_i` contains a single edge of `G`"; for a loop row it is the statement that
the row displays exactly two occurrences and both lie above the leaf edge
(`RowSingleColumnProof.card_rowEdges_core_loop_iff`).  That is **not** weaker:
it is the clause `h_l = ⟨A, e₁, C, e₂, A⟩` of Part II's `lm:bridge-and-loop`,
and saying "both of its occurrences" already presupposes it.

Nothing in this module proves it for any row. -/
def RowSingleColumn (labelling : StableLengthMatrixLabelling data coordinate)
    (sourceRow column : coordinate) : Prop :=
  ∀ edge ∈ rowEdges labelling sourceRow, edge.1.1 = labelling.targetEdge column

omit [Fintype coordinate] in
/-- A row supported in a single column meets no other column. -/
theorem not_meets_of_rowSingleColumn {labelling : StableLengthMatrixLabelling data coordinate}
    {sourceRow column : coordinate} (hSingle : RowSingleColumn labelling sourceRow column)
    {column' : coordinate} (hne : column' ≠ column) :
    ¬ Meets labelling sourceRow column' := by
  rintro ⟨edge, hEdge, hTarget⟩
  exact hne (labelling.targetEdge.injective (hTarget.symm.trans (hSingle edge hEdge)))

omit [Fintype coordinate] in
/-- The matrix form of the previous lemma. -/
theorem matrix_eq_zero_of_rowSingleColumn
    {labelling : StableLengthMatrixLabelling data coordinate}
    {sourceRow column : coordinate} (hSingle : RowSingleColumn labelling sourceRow column)
    {column' : coordinate} (hne : column' ≠ column) :
    GluingDatum.LengthMatrixPresentation.matrix labelling.presentation sourceRow column' = 0 := by
  by_contra hcontra
  exact not_meets_of_rowSingleColumn hSingle hne
    ((matrix_ne_zero_iff_meets labelling sourceRow column').mp hcontra)

/-- **The off-diagonal half of diagonality, derived from the on-diagonal half.**  If
every stable row lies above a single target edge `σ r`, then `σ` is a bijection
from rows to target edges.  The only input beyond `RowSingleColumn` is
nonsingularity of the length matrix, which is a field of the
full-dimensional presentation. -/
theorem column_bijective_of_rowSingleColumn
    (fd : FullDimensionalSourcePresentation data coordinate)
    {σ : coordinate → coordinate}
    (hSingle : ∀ sourceRow, RowSingleColumn fd.labelling sourceRow (σ sourceRow)) :
    Function.Bijective σ :=
  column_bijective_of_det_ne_zero fd.det_ne_zero
    fun r _c hc ↦ matrix_eq_zero_of_rowSingleColumn (hSingle r) hc

/-- **"Distinct stable rows meet distinct columns", in its literal form.** -/
theorem meets_row_unique_of_rowSingleColumn
    (fd : FullDimensionalSourcePresentation data coordinate)
    {σ : coordinate → coordinate}
    (hSingle : ∀ sourceRow, RowSingleColumn fd.labelling sourceRow (σ sourceRow))
    {sourceRow sourceRow' column : coordinate}
    (h : Meets fd.labelling sourceRow column) (h' : Meets fd.labelling sourceRow' column) :
    sourceRow = sourceRow' := by
  have hc : column = σ sourceRow := by
    by_contra hne
    exact not_meets_of_rowSingleColumn (hSingle sourceRow) hne h
  have hc' : column = σ sourceRow' := by
    by_contra hne
    exact not_meets_of_rowSingleColumn (hSingle sourceRow') hne h'
  exact (column_bijective_of_rowSingleColumn fd hSingle).1 (hc ▸ hc' ▸ rfl)

omit [Fintype coordinate] in
/-- Each row does meet the column it is supported in: it has an occurrence
(`SharpRowDenominator.rowEdges_nonempty`), and that occurrence lies there. -/
theorem meets_of_rowSingleColumn {labelling : StableLengthMatrixLabelling data coordinate}
    {sourceRow column : coordinate} (hSingle : RowSingleColumn labelling sourceRow column) :
    Meets labelling sourceRow column := by
  obtain ⟨edge, hEdge⟩ := SharpRowDenominator.rowEdges_nonempty labelling sourceRow
  exact ⟨edge, hEdge, hSingle edge hEdge⟩

/-- **The converse: the off-diagonal half implies the on-diagonal half.**  If
distinct stable rows never meet a common column then, the length matrix being
square and nonsingular, every row is supported in a single column.  So
diagonality is a single obligation, not two independent ones. -/
theorem rowSingleColumn_of_meets_row_unique
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hOff : ∀ sourceRow sourceRow' column : coordinate,
      Meets fd.labelling sourceRow column → Meets fd.labelling sourceRow' column →
        sourceRow = sourceRow') :
    ∃ σ : coordinate → coordinate, Function.Bijective σ ∧
      ∀ sourceRow, RowSingleColumn fd.labelling sourceRow (σ sourceRow) := by
  classical
  obtain ⟨σ, hBij, hIff⟩ := exists_column_perm_of_disjoint fd.det_ne_zero
    (fun r r' hne ↦ by
      rw [Finset.disjoint_left]
      intro c hc hc'
      exact hne (hOff r r' c
        ((matrix_ne_zero_iff_meets fd.labelling r c).mp (mem_rowSupport.mp hc))
        ((matrix_ne_zero_iff_meets fd.labelling r' c).mp (mem_rowSupport.mp hc'))))
  refine ⟨σ, hBij, fun sourceRow edge hEdge ↦ ?_⟩
  have hMeets : Meets fd.labelling sourceRow (fd.labelling.targetEdge.symm edge.1.1) :=
    ⟨edge, hEdge, by rw [Equiv.apply_symm_apply]⟩
  have := (hIff sourceRow (fd.labelling.targetEdge.symm edge.1.1)).mp
    ((matrix_ne_zero_iff_meets fd.labelling sourceRow _).mpr hMeets)
  rw [← this, Equiv.apply_symm_apply]

end S4

/-! ## 4.  The same at an arbitrary member of the fibre -/

section Member

open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
  (member : FibreMember core y degree)

/-- Off-diagonal vanishing of `A_φ` at an arbitrary member. -/
theorem member_matrix_eq_zero_of_ne {σ : Fin p → Fin p}
    (hSingle : ∀ sourceRow, RowSingleColumn member.fullDim.labelling sourceRow (σ sourceRow))
    {sourceRow column : Fin p} (hne : column ≠ σ sourceRow) :
    member.matrix sourceRow column = 0 :=
  matrix_eq_zero_of_rowSingleColumn (hSingle sourceRow) hne

/-- **`A_φ` is a monomial matrix at an arbitrary member.**  The column map of
the diagonality obligation is a bijection of the request's slot type. -/
theorem member_column_bijective {σ : Fin p → Fin p}
    (hSingle : ∀ sourceRow, RowSingleColumn member.fullDim.labelling sourceRow (σ sourceRow)) :
    Function.Bijective σ :=
  column_bijective_of_rowSingleColumn member.fullDim hSingle

/-- Every on-column entry is nonzero. -/
theorem member_matrix_ne_zero {σ : Fin p → Fin p}
    (hSingle : ∀ sourceRow, RowSingleColumn member.fullDim.labelling sourceRow (σ sourceRow))
    (sourceRow : Fin p) :
    member.matrix sourceRow (σ sourceRow) ≠ 0 :=
  entry_ne_zero_of_support member.det_matrix_ne_zero
    (fun r _c hc ↦ matrix_eq_zero_of_rowSingleColumn (hSingle r) hc) sourceRow

/-- **"`A_φ` is diagonal", in the only form that is basis-free:** there is a
permutation of the request's slots after which the length matrix of an
arbitrary fibre member has nonzero entries exactly on the diagonal. -/
theorem exists_perm_member_matrix_diagonal {σ : Fin p → Fin p}
    (hSingle : ∀ sourceRow, RowSingleColumn member.fullDim.labelling sourceRow (σ sourceRow)) :
    ∃ e : Equiv.Perm (Fin p),
      (∀ sourceRow column : Fin p, column ≠ e sourceRow →
        member.matrix sourceRow column = 0) ∧
      (∀ sourceRow : Fin p, member.matrix sourceRow (e sourceRow) ≠ 0) := by
  refine ⟨Equiv.ofBijective σ (member_column_bijective member hSingle), ?_, ?_⟩
  · intro sourceRow column hne
    exact member_matrix_eq_zero_of_ne member hSingle hne
  · intro sourceRow
    exact member_matrix_ne_zero member hSingle sourceRow

/-- **Distinct stable rows meet distinct columns**, at an arbitrary member.
This is the off-diagonal half of Part II's diagonality statement, in its
literal form. -/
theorem member_meets_row_unique {σ : Fin p → Fin p}
    (hSingle : ∀ sourceRow, RowSingleColumn member.fullDim.labelling sourceRow (σ sourceRow))
    {sourceRow sourceRow' column : Fin p}
    (h : Meets member.fullDim.labelling sourceRow column)
    (h' : Meets member.fullDim.labelling sourceRow' column) :
    sourceRow = sourceRow' :=
  meets_row_unique_of_rowSingleColumn member.fullDim hSingle h h'

/-- The converse at an arbitrary member: the off-diagonal statement returns the
on-diagonal one. -/
theorem member_rowSingleColumn_of_meets_row_unique
    (hOff : ∀ sourceRow sourceRow' column : Fin p,
      Meets member.fullDim.labelling sourceRow column →
        Meets member.fullDim.labelling sourceRow' column → sourceRow = sourceRow') :
    ∃ σ : Fin p → Fin p, Function.Bijective σ ∧
      ∀ sourceRow, RowSingleColumn member.fullDim.labelling sourceRow (σ sourceRow) :=
  rowSingleColumn_of_meets_row_unique member.fullDim hOff

end Member

end DraismaVargas.Count.SpineOffDiagonal
