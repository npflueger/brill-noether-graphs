import DraismaVargasCount.SpineOffDiagonal
import DraismaVargasCount.BallotSlopeSeparation

/-!
# Re-indexing a member's columns, and why diagonality is not a class invariant

## The observation

`W4StableSource.StableLengthMatrixLabelling` carries **two independent**
equivalences: `row : StablePath data ≃ coordinate` labels the stable rows, and
`targetEdge : coordinate ≃ target.edges` labels the columns.  Nothing relates
them.  A `FibreMember` stores such a labelling as *data* (inside `fullDim`), so
for every member and every permutation `σ` of the request's slot type there is a
second member with the same target, the same gluing datum, the same core
identification and the same row labelling, whose **columns have been permuted by
`σ`** and whose coordinate vector has been permuted to match.

That second member is `twistColumns σ member` below.  It is open exactly when
`member` is, has the same multiplicity, and -- because
`GeometricMemberIso` has only the three fields `datum`, `overCore_vertex`,
`overCore_row`, none of which mentions the labelling or the coordinates -- it
lies in the **same geometric class**.  So `GeometricFibre.cls`, `openOddCount`
and every class-level statement are untouched by this construction.

What is *not* untouched is `FibreMember.Diagonal`, which says the length matrix
vanishes off the diagonal **in the member's own indexing**.  Twisting by `σ`
replaces `A` by `A.submatrix id σ`, so a diagonal member's twist is diagonal
only for `σ = 1`.

## The consequence, which is the point of this module

A statement asserting that *every* open member of odd multiplicity is `Diagonal`
is inconsistent with the existence of any such member: apply it to a member and to
its twist by a transposition, and the two conclusions contradict each other
(`not_forall_diagonal_of_openOdd`).  Likewise, not every open odd member of the
caterpillar fibre has a ballot core diagonal (`not_forall_extract`).  Statements
about core diagonals must therefore be restricted to diagonal members, as
`BallotSlopes.DiagonalClassification` (module `DiagonalClassification`) is.

The underlying geometry is unaffected.  In Vargas, Part II (arXiv:2609.09109), the
proof of `lm:combinatorial-structure-caterpillar-of-loops` concludes that the
edge-length matrix is diagonal.  For a `FibreMember` the spine argument
(`SpineOffDiagonal.exists_perm_member_matrix_diagonal`)
delivers a **monomial** matrix, `∃ σ, A r c = 0 for c ≠ σ r`, which is exactly
"diagonal up to the labelling of the columns"; `twistColumns_diagonal_of_monomial`
below turns that into an honestly `Diagonal` member of the *same class*.  This is
how the base count finds a diagonal representative in every class
(`CaterpillarAllMembers.exists_diagonal_rep`).

## What is proved

* `twistLabelling`, `twistLabelling_matrix` -- permuting the column labelling
  permutes the columns of the length matrix, and nothing else.
* `twistColumns` -- the twisted member, with `twistColumns_matrix`,
  `twistColumns_coords`, `twistColumns_open_iff`, `twistColumns_absMult`,
  `twistColumns_hasOddMult_iff`, `twistColumns_slotMap`, `twistColumns_cls`.
* `not_diagonal_twistColumns` -- the twist of a diagonal member by a
  non-identity permutation is not diagonal.
* `not_forall_diagonal_of_openOdd` -- **the negative**: over any core with at
  least two slots, "every open odd member is diagonal" implies there is no open
  odd member at all.
* `twistColumns_coreDiag`, `coreDiag_twistColumns_eq_zero` -- the twist reads
  the length matrix off its own support, so a diagonal member's twisted core
  diagonal vanishes wherever the permutation moves the row.
* `not_forall_extract` -- at every positive request over the caterpillar core,
  some open odd member has a core diagonal that is not the ballot diagonal of any
  slope sequence (a twist of the caterpillar member).
* `twistColumns_diagonal_of_monomial`, `exists_diagonal_cls_eq_of_rowSingleColumn`
  -- the monomial conclusion of `SpineOffDiagonal` produces a genuinely
  `Diagonal` member in the same class.

## What is NOT proved here

* Nothing here bears on `CaterpillarBallot.BallotClassification`, whose
  `member_surjective` field is a statement about **classes** and is invariant
  under the twist.
* Nothing here proves `RowSingleColumn` for any row of any member (that is
  `SpineSingleColumn`).
* No member is constructed from nothing: `twistColumns` takes a member and
  returns one, and `not_forall_extract` gets its input member from
  `FibreCaterpillar.caterpillarMember`.
* Nothing here bears on `SlopeRigidity.CoreDiagRigid`,
  `SlopeRigidity.DatumIsoSupply` or `SlopeRigidity.SymmetryRealized`.
-/

namespace DraismaVargas.Count.ColumnTwist

open DraismaVargas.Count
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
variable {target : CFGraph.{0}} {data : GluingDatum target degree}

/-! ## 1.  Permuting the column labelling -/

/-- **The column twist of a stable labelling**: the same row labelling, with the
column labelling precomposed by `σ`. -/
def twistLabelling (labelling : StableLengthMatrixLabelling data (Fin p))
    (σ : Equiv.Perm (Fin p)) : StableLengthMatrixLabelling data (Fin p) where
  targetEdge := σ.trans labelling.targetEdge
  row := labelling.row

@[simp] theorem twistLabelling_row (labelling : StableLengthMatrixLabelling data (Fin p))
    (σ : Equiv.Perm (Fin p)) : (twistLabelling labelling σ).row = labelling.row := rfl

theorem twistLabelling_coefficient (labelling : StableLengthMatrixLabelling data (Fin p))
    (σ : Equiv.Perm (Fin p)) (edge : data.SourceEdge) (column : Fin p) :
    LengthMatrixPresentation.coefficient (twistLabelling labelling σ).presentation edge column =
      LengthMatrixPresentation.coefficient labelling.presentation edge (σ column) := by
  have hsymm : ((twistLabelling labelling σ).presentation.targetEdge).symm edge.1.1 =
      σ.symm ((labelling.presentation.targetEdge).symm edge.1.1) := rfl
  simp only [LengthMatrixPresentation.coefficient]
  by_cases hc : σ column = (labelling.presentation.targetEdge).symm edge.1.1
  · rw [if_pos hc, if_pos (by rw [hsymm, ← hc, Equiv.symm_apply_apply])]
  · refine (if_neg ?_).trans (if_neg hc).symm
    intro h
    exact hc (by rw [h, hsymm, Equiv.apply_symm_apply])

/-- **The twist permutes the columns of the length matrix, and does nothing
else.** -/
theorem twistLabelling_matrix (labelling : StableLengthMatrixLabelling data (Fin p))
    (σ : Equiv.Perm (Fin p)) (sourceRow column : Fin p) :
    LengthMatrixPresentation.matrix (twistLabelling labelling σ).presentation sourceRow column =
      LengthMatrixPresentation.matrix labelling.presentation sourceRow (σ column) := by
  show (List.map (fun edge ↦ LengthMatrixPresentation.coefficient
      (twistLabelling labelling σ).presentation edge column)
      (labelling.presentation.path sourceRow)).sum =
    (List.map (fun edge ↦ LengthMatrixPresentation.coefficient
      labelling.presentation edge (σ column)) (labelling.presentation.path sourceRow)).sum
  exact congrArg List.sum
    (List.map_congr_left fun edge _ ↦ twistLabelling_coefficient labelling σ edge column)

theorem twistLabelling_matrix_eq (labelling : StableLengthMatrixLabelling data (Fin p))
    (σ : Equiv.Perm (Fin p)) :
    LengthMatrixPresentation.matrix (twistLabelling labelling σ).presentation =
      (LengthMatrixPresentation.matrix labelling.presentation).submatrix id σ := by
  funext sourceRow column
  exact twistLabelling_matrix labelling σ sourceRow column

theorem twistLabelling_det_ne_zero (labelling : StableLengthMatrixLabelling data (Fin p))
    (σ : Equiv.Perm (Fin p))
    (hdet : (LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (LengthMatrixPresentation.matrix (twistLabelling labelling σ).presentation).det ≠ 0 := by
  rw [twistLabelling_matrix_eq, Matrix.det_permute']
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simpa using hdet

/-! ## 2.  The column twist of a member -/

/-- **The column twist of a fibre member.**  Same target, same gluing datum,
same core identification, same row labelling; the column labelling is
precomposed with `σ` and the coordinate vector is permuted to match. -/
noncomputable def twistColumns (σ : Equiv.Perm (Fin p))
    (member : FibreMember core y degree) : FibreMember core y degree where
  target := member.target
  data := member.data
  fullDim :=
    { member.fullDim with
      labelling := twistLabelling member.fullDim.labelling σ
      det_ne_zero := twistLabelling_det_ne_zero _ σ member.fullDim.det_ne_zero }
  ident := member.ident
  coords := fun column ↦ member.coords (σ column)
  realizes := by
    have hsub : LengthMatrixPresentation.matrix
        (twistLabelling member.fullDim.labelling σ).presentation =
        member.matrix.submatrix id σ := twistLabelling_matrix_eq _ σ
    have hcomp : (fun column ↦ member.coords (σ column)) ∘ σ.symm = member.coords := by
      funext x
      simp
    show Matrix.mulVec (LengthMatrixPresentation.matrix
        (twistLabelling member.fullDim.labelling σ).presentation)
        (fun column ↦ member.coords (σ column)) = _
    rw [hsub, Matrix.submatrix_mulVec_equiv, hcomp, Function.comp_id]
    exact member.realizes

@[simp] theorem twistColumns_target (σ : Equiv.Perm (Fin p))
    (member : FibreMember core y degree) : (twistColumns σ member).target = member.target := rfl

@[simp] theorem twistColumns_data (σ : Equiv.Perm (Fin p))
    (member : FibreMember core y degree) : (twistColumns σ member).data = member.data := rfl

@[simp] theorem twistColumns_ident (σ : Equiv.Perm (Fin p))
    (member : FibreMember core y degree) : (twistColumns σ member).ident = member.ident := rfl

@[simp] theorem twistColumns_coords (σ : Equiv.Perm (Fin p))
    (member : FibreMember core y degree) (column : Fin p) :
    (twistColumns σ member).coords column = member.coords (σ column) := rfl

theorem twistColumns_matrix (σ : Equiv.Perm (Fin p)) (member : FibreMember core y degree)
    (sourceRow column : Fin p) :
    (twistColumns σ member).matrix sourceRow column = member.matrix sourceRow (σ column) :=
  twistLabelling_matrix _ σ sourceRow column

/-- The row labelling is untouched, so the core-slot dictionary is untouched. -/
@[simp] theorem twistColumns_slotMap (σ : Equiv.Perm (Fin p))
    (member : FibreMember core y degree) : (twistColumns σ member).slotMap = member.slotMap := rfl

/-- **The twist of an open member is open**, `σ` being a bijection. -/
theorem twistColumns_open_iff (σ : Equiv.Perm (Fin p)) (member : FibreMember core y degree) :
    (twistColumns σ member).Open ↔ member.Open := by
  constructor
  · intro h column
    have := h (σ.symm column)
    rwa [twistColumns_coords, Equiv.apply_symm_apply] at this
  · intro h column
    exact h (σ column)

/-- **The multiplicity is untouched.**  Both factors of `Mult φ` are: the row
denominators are least common denominators over all columns, and a column
permutation changes the determinant only by its sign. -/
theorem twistColumns_absMult (σ : Equiv.Perm (Fin p)) (member : FibreMember core y degree) :
    (twistColumns σ member).absMult = member.absMult := by
  have hrow : ∀ sourceRow : Fin p,
      rowDenominator (twistColumns σ member).fullDim.labelling.presentation sourceRow =
        rowDenominator member.fullDim.labelling.presentation sourceRow := by
    intro sourceRow
    show commonDenominator Finset.univ
        (LengthMatrixPresentation.matrix
          (twistLabelling member.fullDim.labelling σ).presentation sourceRow) = _
    rw [show (LengthMatrixPresentation.matrix
        (twistLabelling member.fullDim.labelling σ).presentation sourceRow) =
        fun column ↦ LengthMatrixPresentation.matrix
          member.fullDim.labelling.presentation sourceRow (σ column) from
      funext fun column ↦ twistLabelling_matrix _ σ sourceRow column]
    exact TrivalentWeight.commonDenominator_equiv (σ : Fin p ≃ Fin p) _
  have hden : denominatorProduct (twistColumns σ member).fullDim.labelling.presentation =
      denominatorProduct member.fullDim.labelling.presentation :=
    Finset.prod_congr rfl fun sourceRow _ ↦ hrow sourceRow
  have hdet : |(LengthMatrixPresentation.matrix
      (twistColumns σ member).fullDim.labelling.presentation).det| = |member.matrix.det| := by
    show |(LengthMatrixPresentation.matrix
      (twistLabelling member.fullDim.labelling σ).presentation).det| = _
    rw [twistLabelling_matrix_eq]
    exact Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl (Fin p)) (σ : Fin p ≃ Fin p) _
  show |signedMult (twistColumns σ member).fullDim.labelling.presentation| =
    |signedMult member.fullDim.labelling.presentation|
  unfold signedMult
  rw [abs_mul, abs_mul, hden, hdet]
  rfl

theorem twistColumns_hasOddMult_iff (σ : Equiv.Perm (Fin p))
    (member : FibreMember core y degree) :
    (twistColumns σ member).HasOddMult ↔ member.HasOddMult := by
  unfold FibreMember.HasOddMult
  rw [twistColumns_absMult]

/-- **The twist does not move the geometric class.**  `GeometricMemberIso` has
only the three fields `datum`, `overCore_vertex`, `overCore_row`, and the twist
changes neither the gluing datum nor the core identification nor the row
labelling, so the identity is an isomorphism. -/
theorem twistColumns_cls (σ : Equiv.Perm (Fin p)) (member : FibreMember core y degree) :
    GeometricFibre.cls (twistColumns σ member) = GeometricFibre.cls member := by
  refine GeometricFibre.cls_eq_cls_iff.mpr ⟨⟨GeometricDatumIso.refl member.data, ?_, ?_⟩⟩
  · intro _
    rfl
  · refine Quot.ind ?_
    intro _
    rfl

/-! ## 3.  Diagonality is not a class invariant -/

/-- **The twist of a diagonal member by a non-identity permutation is not
diagonal.**  The entry of the twist at `(a, b)` is the entry of the original at
`(a, a)`, which a diagonal member's nonsingularity forbids to vanish. -/
theorem not_diagonal_twistColumns {σ : Equiv.Perm (Fin p)}
    {member : FibreMember core y degree} (h : member.Diagonal) {a : Fin p} (hne : σ a ≠ a) :
    ¬ (twistColumns σ member).Diagonal := by
  intro htwist
  refine h.matrix_diag_ne_zero a ?_
  have hb : σ.symm a ≠ a := fun hcontra ↦ hne ((Equiv.symm_apply_eq σ).mp hcontra).symm
  have := htwist a (σ.symm a) hb
  rwa [twistColumns_matrix, Equiv.apply_symm_apply] at this

/-- **The negative, over an arbitrary core with at least two slots.**  "Every
open member of odd multiplicity is diagonal" is inconsistent with the existence
of one: the member's twist by a transposition is another open member of odd
multiplicity, and the two cannot both be diagonal. -/
theorem not_forall_diagonal_of_openOdd (hp : 2 ≤ p) (member : FibreMember core y degree)
    (hOpen : member.Open) (hOdd : member.HasOddMult) :
    ¬ (∀ other : FibreMember core y degree, other.Open → other.HasOddMult → other.Diagonal) := by
  intro hdiag
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin p, a ≠ b := by
    have : 1 < p := hp
    exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  refine not_diagonal_twistColumns (σ := Equiv.swap a b) (hdiag member hOpen hOdd)
    (a := a) (by rw [Equiv.swap_apply_left]; exact hab.symm) ?_
  exact hdiag (twistColumns (Equiv.swap a b) member)
    ((twistColumns_open_iff _ member).mpr hOpen)
    ((twistColumns_hasOddMult_iff _ member).mpr hOdd)

/-- The core diagonal of a twist is the original matrix read along `σ`. -/
theorem twistColumns_coreDiag (σ : Equiv.Perm (Fin p)) (member : FibreMember core y degree)
    (slot : Fin p) :
    (twistColumns σ member).coreDiag slot =
      member.matrix (member.slotMap.symm slot) (σ (member.slotMap.symm slot)) :=
  twistColumns_matrix σ member _ _

/-- **A twist moves the core diagonal off the matrix's support**: at every slot
whose row index `σ` moves, the twist of a diagonal member reads `0`. -/
theorem coreDiag_twistColumns_eq_zero {σ : Equiv.Perm (Fin p)}
    {member : FibreMember core y degree} (h : member.Diagonal) (slot : Fin p)
    (hne : σ (member.slotMap.symm slot) ≠ member.slotMap.symm slot) :
    (twistColumns σ member).coreDiag slot = 0 := by
  rw [twistColumns_coreDiag]
  exact h _ _ hne

/-! ## 4.  At the caterpillar core: core diagonals need not be ballot diagonals -/

open DraismaVargas.Count.FibreCaterpillar

/-- **Not every open odd member has a ballot core diagonal.**
The twist of the caterpillar member by the transposition of slots `0` and `1`
reads `0` at slot `0`, while `ballotCoreDiag m s` reads `2` there for every
slope sequence, slot `0` being a leaf edge.

So restricting this statement to *diagonal* members, as
`BallotSlopes.DiagonalClassification` does, is necessary and not merely
convenient. -/
theorem not_forall_extract {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    ¬ (∀ mem : FibreMember (catCore m) request (m + 2), mem.Open → mem.HasOddMult →
        ∃ s : Slopes (2 * (m + 1)), mem.coreDiag = BallotSlopes.ballotCoreDiag m s) := by
  intro hextract
  have ha : (0 : ℕ) < 6 * m + 3 := by omega
  have hb : (1 : ℕ) < 6 * m + 3 := by omega
  obtain ⟨s, hs⟩ := hextract
    (twistColumns (Equiv.swap ⟨0, ha⟩ ⟨1, hb⟩) (caterpillarMember m request))
    ((twistColumns_open_iff _ _).mpr (caterpillarMember_open hRequest))
    ((twistColumns_hasOddMult_iff _ _).mpr (caterpillarMember_hasOddMult m request))
  have hzero : (twistColumns (Equiv.swap (⟨0, ha⟩ : Fin (6 * m + 3)) ⟨1, hb⟩)
      (caterpillarMember m request)).coreDiag ⟨0, ha⟩ = 0 := by
    rw [twistColumns_coreDiag, slotMap_symm_caterpillarMember, Equiv.swap_apply_left]
    exact diagonal_caterpillarMember m request _ _ (by simp)
  rw [congrFun hs ⟨0, ha⟩,
    BallotSlopes.ballotCoreDiag_leaf s (Or.inl (by simp))] at hzero
  norm_num at hzero

/-! ## 5.  A monomial matrix gives a diagonal member -/

/-- **A monomial member has a diagonal twist.**  This is the honest reading of
"`A_φ` is diagonal": `SpineOffDiagonal.exists_perm_member_matrix_diagonal`
produces the permutation, and twisting by it produces a member that is
`Diagonal` on the nose. -/
theorem twistColumns_diagonal_of_monomial {σ : Equiv.Perm (Fin p)}
    {member : FibreMember core y degree}
    (hmon : ∀ sourceRow column : Fin p, column ≠ σ sourceRow → member.matrix sourceRow column = 0) :
    (twistColumns σ member).Diagonal := by
  intro sourceRow column hne
  rw [twistColumns_matrix]
  exact hmon sourceRow (σ column) fun hcontra ↦ hne (σ.injective hcontra)

/-- **Single-column rows supply a diagonal member of the same class.**  Given the single
obligation `RowSingleColumn` on every stable row of an open member of odd
multiplicity, there is a genuinely `Diagonal` open member of odd multiplicity in
the same geometric class. -/
theorem exists_diagonal_cls_eq_of_rowSingleColumn (member : FibreMember core y degree)
    (hOpen : member.Open) (hOdd : member.HasOddMult) {σ : Fin p → Fin p}
    (hSingle : ∀ sourceRow,
      SpineOffDiagonal.RowSingleColumn member.fullDim.labelling sourceRow (σ sourceRow)) :
    ∃ other : FibreMember core y degree,
      other.Open ∧ other.HasOddMult ∧ other.Diagonal ∧
        GeometricFibre.cls other = GeometricFibre.cls member := by
  obtain ⟨e, hzero, _⟩ := SpineOffDiagonal.exists_perm_member_matrix_diagonal member hSingle
  exact ⟨twistColumns e member, (twistColumns_open_iff e member).mpr hOpen,
    (twistColumns_hasOddMult_iff e member).mpr hOdd,
    twistColumns_diagonal_of_monomial hzero, twistColumns_cls e member⟩

end DraismaVargas.Count.ColumnTwist
