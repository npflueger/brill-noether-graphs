import DraismaVargasCount.BaseCountParity
import DraismaVargasCount.LollipopBridgeFibreWitness
import DraismaVargasCount.NonTrivalentCorner

/-!
# The `extract` field of `DiagonalClassification`: the loop slots, and genus two

The `extract` field of `BallotSlopes.DiagonalClassification` -- named as a standalone
proposition, `BallotSlopes.DiagonalExtract m request`, in `DiagonalExtract` -- asks that the core
diagonal of every diagonal open member of odd multiplicity over the caterpillar of loops
`catCore m` be the ballot diagonal of some slope sequence.  This module proves the part of it
that concerns the loop slots, at every genus, and the whole field at genus two (`m = 0`), for
every member: no request hypothesis, no `Open`, no `HasOddMult`.

## The two ingredients

1. `LeafFibre.matrix_leafEdge_column` says the `t_v` column of `A_φ` is `2 · e_{h(v)}`, for
   every member and with no hypothesis whatsoever.  For a **diagonal** member the nonzero entry
   of that column must sit on the diagonal, so the leaf column *is* the loop slot's own column
   and the entry is its `coreDiag`.  That is `coreDiag_eq_two_of_loop` below, and it is general
   in the core and the genus.
2. `LollipopBridgeFibreWitness.exists_bridge_loopBranch` produces, at every member and every
   self-loop slot of the core, a surviving occurrence `e_b` incident to the loop branch `A`, off
   the loop row, with `sourceEdgeIndex e_b = 2`, and carries no hypothesis beyond
   `core.tail slot = core.head slot`.

Given those two, the bridge value is a three-line argument that never mentions the length-two
clause of Part II's `lm:bridge-and-loop`:

* `e_b` survives, so it is displayed on exactly one stable row `r`;
* the member is diagonal, so row `r` is supported at column `r` and every occurrence displayed on
  it lies above `targetEdge r` (`NonTrivalentCorner.target_eq_of_supported`) -- in particular
  `e_b` does;
* if `targetEdge r` were a leaf edge then `m(e_b) = 1`
  (`LeafFibre.sourceEdgeIndex_eq_one_above_leaf`), contradicting `m(e_b) = 2`; so column `r` is
  **not** a leaf column, and `NonTrivalentCorner.corner_eq_reciprocal_of_nonleaf` says the row
  meets that column in the single occurrence `e_b` with entry `1 / m(e_b) = 1 / 2`.

## Main results

* `coreDiag_eq_two_of_loop` -- **at every genus and over every core**, a diagonal member reads
  `2` at every self-loop slot.  No request hypothesis, no `Open`, no `HasOddMult`, no
  genericity.
* `exists_coreDiag_eq_half_of_loop` -- **at every genus and over every core**, each self-loop
  slot supplies a *different* slot whose diagonal entry is `1 / 2`: the slot of the stable row
  carrying the loop's bridge occurrence.
* `coreDiag_eq_ballotCoreDiag_of_isLeafEdge` -- over `catCore m` the core diagonal of a diagonal
  member **already agrees with every ballot diagonal on all `2m + 2` leaf slots**, at every `m`.
* `diagonalExtract_of_forall_not_isLeafEdge`, `diagonalExtract_iff_forall_not_isLeafEdge` --
  consequently, at every `m`, the `extract` field **is** its restriction to the `4m + 1`
  non-leaf slots.  This reduction is what `DiagonalClassificationGenusSix` uses at genus six.
* `coreDiag_apply_genusTwo` -- at `m = 0` the two ingredients combine to pin the whole core
  diagonal: `coreDiag slot = if IsLeafEdge 0 slot then 2 else 1 / 2`.
* `ballotCoreDiag_genusTwo` -- and that is the value of `ballotCoreDiag 0 s`, for **every** `s`,
  because `Slopes 2` forces `s₁ = 2` through `Slopes.slope_of_ge`.
* `coreDiag_eq_ballotCoreDiag_genusTwo`, `extract_of_diagonal_genusTwo`,
  `diagonalExtract_genusTwo` -- **the `extract` field at `m = 0`**, from diagonality alone.
* `exists_open_odd_diagonal_genusTwo` -- at a positive request the caterpillar member is open,
  odd **and diagonal**, so the genus-two `extract` is a statement about a nonempty set of
  members.
* `diagonalClassification_genusTwo_of_rigid` -- `DiagonalClassification 0` from the `rigid`
  field alone, the `diagonal` field coming from `BaseCountParity.diagonal_genusTwo`.

## Remarks

* **Beyond the leaf slots, nothing here is about `m ≥ 1`.**  `coreDiag_eq_two_of_loop` and
  `exists_coreDiag_eq_half_of_loop` are general, but the *identification of which slot* carries
  the `1 / 2` uses that `Fin (6 * 0 + 3)` has three elements and two of them are leaf slots.  At
  `m ≥ 1` the same two lemmas give `2` on the `2m + 2` leaf slots and a `1 / 2` somewhere off
  them, and say **nothing** about the spine slots, which is where the slope sequence lives.  The
  genus-two coincidence is exactly this: at `m = 0` there is no spine slot at all, so `extract`
  never has to produce a slope.
* **`Diagonal` is essential.**  Every statement below assumes it;
  `ColumnTwist.not_forall_extract` refutes the unrestricted form.
* **`Open` and `HasOddMult` are not used anywhere below**, which makes the genus-two `extract`
  stronger than the field requires.  That is not evidence that they are removable at `m ≥ 1`.
* Nothing here constructs a member.  Over an empty open odd fibre the conclusions below are
  still true but vacuous as count statements; non-vacuity at a positive request is
  `GeometricFibre.caterpillar_openOddCount_pos`, and is not used.
-/

namespace DraismaVargas.Count.ExtractGenusTwo

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.Count.FibreCaterpillar (catCore)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-! ## 1.  A diagonal member reads `2` at every self-loop slot -/

/-- The core-slot dictionary, unfolded: `slotMap.symm` sends a core slot to the
matrix row of that slot's stable path. -/
theorem slotMap_symm_apply (member : FibreMember core y degree) (slot : Fin p) :
    member.slotMap.symm slot =
      member.fullDim.labelling.row (member.ident.row.symm slot) := rfl

/-- **At every genus and over every core, a diagonal member reads `2` at a
self-loop slot.**

`LollipopLeafRow.leafRow_loopLeaf` identifies the slot's matrix row with the
leaf row `h(v)` of the leaf `v` the loop passes above, and
`LeafFibre.matrix_leafEdge_column` says the `t_v` column of the matrix is `2`
on that row and `0` off it.  Diagonality then forces the `t_v` column to *be*
the row's own column, so the `2` is the diagonal entry.

No hypothesis on the request, and none on the member beyond `Diagonal`: not
`Open`, not `HasOddMult`, not genericity. -/
theorem coreDiag_eq_two_of_loop (member : FibreMember core y degree)
    (hD : member.Diagonal) {slot : Fin p} (hLoop : core.tail slot = core.head slot) :
    member.coreDiag slot = 2 := by
  have hLeaf := LollipopLeafRow.loopLeaf_isLeafVertex member hLoop
  have hLeafRow : LeafFibre.leafRow member.fullDim hLeaf = member.slotMap.symm slot :=
    LollipopLeafRow.leafRow_loopLeaf member hLoop
  have hcol := LeafFibre.matrix_leafEdge_column member.fullDim hLeaf
    (member.slotMap.symm slot)
  rw [if_pos hLeafRow.symm] at hcol
  have hEq : member.fullDim.labelling.targetEdge.symm (leafEdge hLeaf) =
      member.slotMap.symm slot := by
    by_contra hne
    have hzero : GluingDatum.LengthMatrixPresentation.matrix
        member.fullDim.labelling.presentation (member.slotMap.symm slot)
        (member.fullDim.labelling.targetEdge.symm (leafEdge hLeaf)) = 0 :=
      hD _ _ hne
    rw [hzero] at hcol
    norm_num at hcol
  rw [hEq] at hcol
  exact hcol

/-! ## 2.  Each self-loop slot supplies another slot reading `1 / 2` -/

/-- **At every genus and over every core, a self-loop slot supplies a second
slot whose diagonal entry is `1 / 2`.**

The bridge occurrence `e_b` at the loop branch has `m(e_b) = 2`
(`LollipopBridgeFibreWitness.exists_bridge_loopBranch`, unconditional).  It
survives, so it is displayed on one stable row `r`; diagonality supports row
`r` at column `r`, so `e_b` lies above `targetEdge r`; that target edge is not
a leaf edge, since every occurrence above a leaf edge is unramified and
`m(e_b) = 2`; so column `r` is not a leaf column and the row meets it in the
single occurrence `e_b`, with entry `1 / m(e_b) = 1 / 2`.

The returned slot differs from the loop slot because §1 reads `2` there. -/
theorem exists_coreDiag_eq_half_of_loop (member : FibreMember core y degree)
    (hD : member.Diagonal) {slot : Fin p} (hLoop : core.tail slot = core.head slot) :
    ∃ stem : Fin p, stem ≠ slot ∧ member.coreDiag stem = 1 / 2 := by
  classical
  obtain ⟨bridge, hSurv, _hInc, _hOff, hIdx⟩ :=
    LollipopBridgeFibreWitness.exists_bridge_loopBranch member hLoop
  set r := member.fullDim.labelling.row
    (NonDanglingEdge.stablePath (⟨bridge, hSurv⟩ : NonDanglingEdge member.data)) with hr
  have hmem : bridge ∈ EdgeDenominator.rowEdges member.fullDim.labelling r :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨hSurv, rfl⟩
  have hSupport : ∀ j, j ≠ r → GluingDatum.LengthMatrixPresentation.matrix
      member.fullDim.labelling.presentation r j = 0 := fun j hj ↦ hD r j hj
  have hTarget : bridge.1.1 = member.fullDim.labelling.targetEdge r :=
    NonTrivalentCorner.target_eq_of_supported member.fullDim.labelling hSupport hmem
  have hNonleaf : r ∉ leafColumns member.fullDim.labelling.presentation := by
    intro hcol
    obtain ⟨v, hv, hincid⟩ := (mem_leafColumns _ _).mp hcol
    have hleafedge : bridge.1.1 = leafEdge hv := by
      rw [hTarget]; exact eq_leafEdge_of_mem hv hincid
    have hone := LeafFibre.sourceEdgeIndex_eq_one_above_leaf member.fullDim hv hleafedge
    omega
  obtain ⟨e, _he, hfibre, hval⟩ :=
    NonTrivalentCorner.corner_eq_reciprocal_of_nonleaf member.fullDim hSupport hNonleaf
  have hbf : bridge ∈ LeafFibre.rowFibre member.fullDim.labelling r
      (member.fullDim.labelling.targetEdge r) :=
    (EdgeDenominator.mem_rowFibre_iff _ _ _ _).mpr ⟨hmem, hTarget⟩
  rw [hfibre, Finset.mem_singleton] at hbf
  have hhalf : member.coreDiag (member.slotMap r) = 1 / 2 := by
    have hsymm : member.slotMap.symm (member.slotMap r) = r := member.slotMap.symm_apply_apply r
    show GluingDatum.LengthMatrixPresentation.matrix member.fullDim.labelling.presentation
      (member.slotMap.symm (member.slotMap r)) (member.slotMap.symm (member.slotMap r)) = 1 / 2
    rw [hsymm, hval, ← hbf, hIdx]
    norm_num
  refine ⟨member.slotMap r, ?_, hhalf⟩
  rintro rfl
  rw [coreDiag_eq_two_of_loop member hD hLoop] at hhalf
  norm_num at hhalf

/-! ## 3.  Over `catCore m`: the leaf slots already agree with every ballot
diagonal -/

section Caterpillar

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-- The self-loop slots of `catCore m` are its leaf slots, so §1 reads `2` on
all `2m + 2` of them. -/
theorem coreDiag_eq_two_of_isLeafEdge (member : FibreMember (catCore m) request (m + 2))
    (hD : member.Diagonal) {slot : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m slot) :
    member.coreDiag slot = 2 :=
  coreDiag_eq_two_of_loop member hD ((LollipopLeafRow.catCore_tail_eq_head_iff m slot).mpr hLeaf)

/-- **At every `m`, a diagonal member's core diagonal already agrees with every
ballot diagonal on the leaf slots.**  What `extract` still owes is the
`4m + 1` non-leaf slots -- the spine slots, where the slope sequence lives, and
the stems. -/
theorem coreDiag_eq_ballotCoreDiag_of_isLeafEdge
    (member : FibreMember (catCore m) request (m + 2)) (hD : member.Diagonal)
    (s : Slopes (2 * (m + 1))) {slot : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m slot) :
    member.coreDiag slot = BallotSlopes.ballotCoreDiag m s slot := by
  rw [coreDiag_eq_two_of_isLeafEdge member hD hLeaf, BallotSlopes.ballotCoreDiag_leaf s hLeaf]

/-- **`extract` reduces to the non-leaf slots, at every `m`.**  The `2m + 2`
leaf slots are free by §1, so the whole content of the `extract` field lies on
the `4m + 1` spine and stem slots. -/
theorem diagonalExtract_of_forall_not_isLeafEdge
    (h : ∀ member : FibreMember (catCore m) request (m + 2),
      member.Open → member.HasOddMult → member.Diagonal →
        ∃ s : Slopes (2 * (m + 1)), ∀ slot : Fin (6 * m + 3), ¬ IsLeafEdge m slot →
          member.coreDiag slot = BallotSlopes.ballotCoreDiag m s slot) :
    BallotSlopes.DiagonalExtract m request := by
  intro member hOpen hOdd hD
  obtain ⟨s, hs⟩ := h member hOpen hOdd hD
  refine ⟨s, funext fun slot ↦ ?_⟩
  by_cases hLeaf : IsLeafEdge m slot
  · exact coreDiag_eq_ballotCoreDiag_of_isLeafEdge member hD s hLeaf
  · exact hs slot hLeaf

/-- And the reduction loses nothing. -/
theorem diagonalExtract_iff_forall_not_isLeafEdge :
    BallotSlopes.DiagonalExtract m request ↔
      ∀ member : FibreMember (catCore m) request (m + 2),
        member.Open → member.HasOddMult → member.Diagonal →
          ∃ s : Slopes (2 * (m + 1)), ∀ slot : Fin (6 * m + 3), ¬ IsLeafEdge m slot →
            member.coreDiag slot = BallotSlopes.ballotCoreDiag m s slot :=
  ⟨fun hextract member hOpen hOdd hD ↦ by
      obtain ⟨s, hs⟩ := hextract member hOpen hOdd hD
      exact ⟨s, fun slot _ ↦ congrFun hs slot⟩,
    diagonalExtract_of_forall_not_isLeafEdge⟩

end Caterpillar

/-! ## 4.  Genus two: the whole core diagonal, and `extract` -/

section GenusTwo

variable {request : Fin (6 * 0 + 3) → ℚ}

theorem loop_zero : (catCore 0).tail 0 = (catCore 0).head 0 :=
  (LollipopLeafRow.catCore_tail_eq_head_iff 0 0).mpr (by decide)

theorem loop_two : (catCore 0).tail 2 = (catCore 0).head 2 :=
  (LollipopLeafRow.catCore_tail_eq_head_iff 0 2).mpr (by decide)

/-- **The core diagonal of a diagonal member at genus two, pinned.**  Slots `0`
and `2` are the two self-loops and read `2`; the `1 / 2` produced by §2 can only
sit on the one remaining slot. -/
theorem coreDiag_apply_genusTwo (member : FibreMember (catCore 0) request (0 + 2))
    (hD : member.Diagonal) (slot : Fin (6 * 0 + 3)) :
    member.coreDiag slot = if IsLeafEdge 0 slot then 2 else 1 / 2 := by
  have h0 : member.coreDiag 0 = 2 := coreDiag_eq_two_of_loop member hD loop_zero
  have h2 : member.coreDiag 2 = 2 := coreDiag_eq_two_of_loop member hD loop_two
  obtain ⟨stem, _hne, hstem⟩ := exists_coreDiag_eq_half_of_loop member hD loop_zero
  have hstem0 : stem ≠ 0 := by
    rintro rfl
    rw [h0] at hstem
    norm_num at hstem
  have hstem2 : stem ≠ 2 := by
    rintro rfl
    rw [h2] at hstem
    norm_num at hstem
  have hstem1 : stem = 1 := by
    fin_cases stem
    · exact absurd rfl hstem0
    · rfl
    · exact absurd rfl hstem2
  rw [hstem1] at hstem
  fin_cases slot
  · rw [if_pos (by decide)]; exact h0
  · rw [if_neg (by decide)]; exact hstem
  · rw [if_pos (by decide)]; exact h2

/-- **Every ballot diagonal at genus two is `(2, 1/2, 2)`.**  `Slopes 2` has a
single slope and `Slopes.slope_of_ge` forces it to be `2`, so the spine slot
reads `1 / s₁ = 1 / 2`. -/
theorem ballotCoreDiag_genusTwo (s : Slopes (2 * (0 + 1))) (slot : Fin (6 * 0 + 3)) :
    BallotSlopes.ballotCoreDiag 0 s slot = if IsLeafEdge 0 slot then 2 else 1 / 2 := by
  by_cases hLeaf : IsLeafEdge 0 slot
  · rw [if_pos hLeaf, BallotSlopes.ballotCoreDiag_leaf s hLeaf]
  · rw [if_neg hLeaf]
    have hmod : slot.val % 3 = 1 := by
      unfold IsLeafEdge at hLeaf
      omega
    rw [BallotSlopes.ballotCoreDiag_spine s hmod,
      show (slot.val + 2) / 3 = 1 by omega, Slopes.slope_of_ge s (by omega)]
    norm_num

/-- **The `extract` field at genus two, over every diagonal member.** -/
theorem coreDiag_eq_ballotCoreDiag_genusTwo (member : FibreMember (catCore 0) request (0 + 2))
    (hD : member.Diagonal) (s : Slopes (2 * (0 + 1))) :
    member.coreDiag = BallotSlopes.ballotCoreDiag 0 s :=
  funext fun slot ↦
    (coreDiag_apply_genusTwo member hD slot).trans (ballotCoreDiag_genusTwo s slot).symm

/-- **`extract` at `m = 0`, from diagonality alone**: no request hypothesis,
no `Open`, no `HasOddMult`. -/
theorem extract_of_diagonal_genusTwo (member : FibreMember (catCore 0) request (0 + 2))
    (hD : member.Diagonal) :
    ∃ s : Slopes (2 * (0 + 1)), member.coreDiag = BallotSlopes.ballotCoreDiag 0 s :=
  ⟨BallotDatum.zig 0, coreDiag_eq_ballotCoreDiag_genusTwo member hD _⟩

/-- **`BallotSlopes.DiagonalExtract 0 request`**, the `extract` field of
`BallotSlopes.DiagonalClassification` named as a standalone proposition in
`DiagonalExtract`, at genus two. -/
theorem diagonalExtract_genusTwo : BallotSlopes.DiagonalExtract 0 request :=
  fun member _ _ hD ↦ extract_of_diagonal_genusTwo member hD

/-- **The genus-two `extract` is not vacuous.**  At a positive request the
caterpillar member is open, of odd multiplicity **and diagonal**, so
`extract_of_diagonal_genusTwo` applies to an actual member.  (`Open` and
`HasOddMult` are recorded here only to bound the witness; the `extract`
statement above uses neither.) -/
theorem exists_open_odd_diagonal_genusTwo (hRequest : ∀ slot, 0 < request slot) :
    ∃ member : FibreMember (catCore 0) request (0 + 2),
      member.Open ∧ member.HasOddMult ∧ member.Diagonal :=
  ⟨FibreCaterpillar.caterpillarMember 0 request,
    FibreCaterpillar.caterpillarMember_open hRequest,
    FibreCaterpillar.caterpillarMember_hasOddMult 0 request,
    FibreCaterpillar.diagonal_caterpillarMember 0 request⟩

/-! ## 5.  `DiagonalClassification 0` from `rigid` -/

/-- **`DiagonalClassification 0 request` from the `rigid` field alone.**  Its
`diagonal` field is `BaseCountParity.diagonal_genusTwo` and its `extract` field
is §4. -/
theorem diagonalClassification_genusTwo_of_rigid
    (rigid : ∀ first second : FibreMember (catCore 0) request (0 + 2),
      first.Open → first.HasOddMult → first.Diagonal →
        second.Open → second.HasOddMult → second.Diagonal →
          first.coreDiag = second.coreDiag →
            GeometricFibre.cls first = GeometricFibre.cls second) :
    BallotSlopes.DiagonalClassification 0 request :=
  BaseCountParity.diagonalClassification_genusTwo_of_extract_rigid
    (fun member _ _ hD ↦ extract_of_diagonal_genusTwo member hD) rigid

end GenusTwo

end DraismaVargas.Count.ExtractGenusTwo
