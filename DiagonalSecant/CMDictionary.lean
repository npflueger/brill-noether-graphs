module

public import DiagonalSecant.Defs
public import DraismaVargasMarkedCount.MarkedCountGeneral.Correspondence
public import DraismaVargasCount.OddDenominator

@[expose] public section

/-!
# The regrowth dictionary for the matrix

For a typed frame `κ` of a lower type over a marked-cubic core with a tailed core `T` at the
headline degree, the regrown frame `f := regrowTailed T hc hd J κ s` (the regrowth of the
two-point ramified count) is an unmarked frame of `T.H`, and this module reads `f`'s matrix data
back on `κ`:

* the labelling (`targetEdge_coreSlot`, `slot_coreSlot`, `slot_tailSlot`): the core columns of
  `f` are `κ`'s columns, and the core rows of `f` are `κ`'s rows, through `T.slotEquiv`;
* the coordinates (`coordsAt_regrowTailed`): at the request `T.request y` (tails of length `1`)
  the coordinate vector of `f` is `κ.coordsAt y` on the core columns and `1 / tailDiag` on the
  tail columns, because the matrix is block diagonal (`CatRegrow.matrix_labelling`); its right
  side is integral when `y` is (`mulVec_regrowCoords_int`);
* the multiplicity (`absMult_regrowTailed`, `odd_fdAbsMultNat`): `|Mult f| = |Mult(κ; marks)|`,
  the multiplicity identity of the two-point ramified count, read through
  `restrictTailed_regrowTailed` and `mult_tailedClassEquiv`;
* the leaf columns (`mem_leafColumns_of_coreSlot`): a core column that is a leaf column of `f`
  is a leaf column of `κ` (the tails only add valency at the old vertices);
* hence **the odd denominators** (`odd_leafAdjustedCoords_den_of_regrow`): when `|Mult(κ; marks)|`
  is odd, every leaf-adjusted coordinate of `κ` at an integral request has odd denominator, by
  `OddDenominator.odd_leafAdjustedCoords_den` on `f`. This gives
  `TypedMoments.odd_leafAdjustedCoords_den_of_model`.

No positivity is used anywhere: the public odd-denominator lemma holds on closed faces.
-/

namespace DiagonalSecant.CM

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.MarkedCountGeneral.CatRegrow
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.SlotMoment (oddDenominatorSubring mem_oddDenominatorSubring)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 0.  Slope sequences without ascents, and casts -/

/-- The descending slope sequence `a + 1, a, …, 2`: the one slope sequence with no ascent. -/
def zeroSlope (a : ℕ) {j : ℕ} (hj : j = 0) : SlopeSeq a j :=
  ⟨fun i ↦ a + 1 - i.val, by
    subst hj
    refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, fun i i' hi' ↦ Or.inr ?_, fun i hi ↦ ?_⟩ <;> dsimp only
    · have := i.isLt; omega
    · omega
    · have := i'.isLt; omega
    · omega⟩

/-- Oddness of a leaf-adjusted denominator is invariant under the cast of a typed frame. -/
theorem odd_leafAdjusted_cast_iff {n p k : ℕ} {core : Core n p} {mark : Fin k → Fin n}
    {types types' : Fin k → ℕ} {d d' : ℕ} (ht : types = types') (hd : d = d')
    (κ : TypedFrame core mark types d) (z : Fin p → ℚ) (col : Fin p) :
    Odd (OddDenominator.leafAdjustedCoords
      (TypedFrame.cast ht hd κ).fullDim.labelling.presentation z col).den ↔
    Odd (OddDenominator.leafAdjustedCoords κ.fullDim.labelling.presentation z col).den := by
  subst ht hd
  rfl

/-! ## 1.  The labelling of the regrown frame on the core part -/

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) (hd : IsTailDegree n p c degree)
  (J : LowerIndex c) (κ : TypedFrame core mark (lowerType c J) (degree - shed J))
  (s : SlopeData c J)

theorem fullDim_regrowTailed :
    (regrowTailed T hc hd J κ s).fullDim = CatRegrow.fullDim T hd J κ s hc := rfl

/-- A core column of `f` is the old copy of the same column of `κ`. -/
theorem targetEdge_coreSlot (i : Fin p) :
    (regrowTailed T hc hd J κ s).fullDim.labelling.targetEdge (T.coreSlot i) =
      oldE c (CatRegrow.branching hd J κ s).x (κ.fullDim.labelling.targetEdge i) := by
  show (T.slotEquiv.symm.trans (colEquiv hd J κ s)) (T.slotEquiv (Sum.inl i)) = _
  rw [Equiv.trans_apply, Equiv.symm_apply_apply, colEquiv_inl]

/-- The slot permutation of `f` is `κ`'s on the core rows. -/
theorem slot_coreSlot (r : Fin p) :
    (regrowTailed T hc hd J κ s).slot (T.coreSlot r) = T.coreSlot (κ.slot r) := by
  show (CatRegrow.ident T hd J κ s hc).row
    ((CatRegrow.labelling T hd J κ s).row.symm (T.slotEquiv (Sum.inl r))) =
    T.slotEquiv (Sum.inl (κ.ident.row (κ.fullDim.labelling.row.symm r)))
  simp [CatRegrow.ident, CatRegrow.labelling, CatRegrow.labRow, CatRegrow.identRow]

/-- The slot permutation of `f` is the identity on the tail rows. -/
theorem slot_tailSlot (j : Fin k) (t : CatSlot (c j)) :
    (regrowTailed T hc hd J κ s).slot (T.tailSlot j t) = T.tailSlot j t := by
  show (CatRegrow.ident T hd J κ s hc).row
    ((CatRegrow.labelling T hd J κ s).row.symm (T.slotEquiv (Sum.inr ⟨j, t⟩))) =
    T.slotEquiv (Sum.inr ⟨j, t⟩)
  simp [CatRegrow.ident, CatRegrow.labelling, CatRegrow.labRow, CatRegrow.identRow]

/-- The matrix of `f` is the block matrix of `κ`'s marked matrix and the tail diagonal. -/
theorem matrix_regrowTailed :
    (regrowTailed T hc hd J κ s).matrix =
      (blockMatrix hd J κ s).submatrix T.slotEquiv.symm T.slotEquiv.symm :=
  matrix_labelling T hd J κ s

/-! ## 2.  The coordinates at a request with unit tails -/

/-- **The coordinate vector of the regrown frame** at `T.request y`: `κ`'s coordinates on the
core columns, `1 / tailDiag` on the tail columns. -/
noncomputable def regrowCoords (y : Fin p → ℚ) : Fin T.P → ℚ := fun e ↦
  Sum.elim (κ.coordsAt y) (fun t ↦ 1 / (CatRegrow.branching hd J κ s).tailDiag t)
    (T.slotEquiv.symm e)

@[simp] theorem regrowCoords_coreSlot (y : Fin p → ℚ) (i : Fin p) :
    regrowCoords T hd J κ s y (T.coreSlot i) = κ.coordsAt y i := by
  simp [regrowCoords, Tailed.coreSlot]

@[simp] theorem regrowCoords_tailSlot (y : Fin p → ℚ) (j : Fin k) (t : CatSlot (c j)) :
    regrowCoords T hd J κ s y (T.tailSlot j t) =
      1 / (CatRegrow.branching hd J κ s).tailDiag ⟨j, t⟩ := by
  simp [regrowCoords, Tailed.tailSlot]

/-- `regrowCoords` solves the length system of `f` at `T.request y`. -/
theorem mulVec_regrowCoords (y : Fin p → ℚ) :
    (regrowTailed T hc hd J κ s).matrix.mulVec (regrowCoords T hd J κ s y) =
      fun row ↦ T.request y ((regrowTailed T hc hd J κ s).slot row) := by
  rw [matrix_regrowTailed, Matrix.submatrix_mulVec_equiv]
  have hv : regrowCoords T hd J κ s y ∘ T.slotEquiv.symm.symm =
      Sum.elim (κ.coordsAt y)
        (fun t ↦ 1 / (CatRegrow.branching hd J κ s).tailDiag t) := by
    funext z
    simp [regrowCoords]
  rw [hv]
  funext row
  obtain ⟨z, rfl⟩ := T.slotEquiv.surjective row
  simp only [Function.comp, Equiv.symm_apply_apply, blockMatrix, Matrix.fromBlocks_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, add_zero, zero_add]
  rcases z with r | ⟨j, t⟩
  · rw [Sum.elim_inl, show T.slotEquiv (Sum.inl r) = T.coreSlot r from rfl, slot_coreSlot,
      Tailed.request_coreSlot]
    exact congrFun (κ.mulVec_coordsAt y) r
  · rw [Sum.elim_inr, show T.slotEquiv (Sum.inr ⟨j, t⟩) = T.tailSlot j t from rfl, slot_tailSlot,
      Tailed.request_tailSlot, Matrix.mulVec_diagonal]
    exact mul_one_div_cancel ((CatRegrow.branching hd J κ s).tailDiag_pos ⟨j, t⟩).ne'

/-- **The coordinates of the regrown frame at `T.request y`** are `regrowCoords`. -/
theorem coordsAt_regrowTailed (y : Fin p → ℚ) :
    (regrowTailed T hc hd J κ s).coordsAt (T.request y) = regrowCoords T hd J κ s y :=
  (((regrowTailed T hc hd J κ s).member (T.request y)).coords_unique _
    (mulVec_regrowCoords T hc hd J κ s y)).symm

/-- The integral right side of the length system of `f` at an integral request. -/
def regrowRequestInt (yZ : Fin p → ℤ) : Fin T.P → ℤ := fun e ↦
  Sum.elim (fun r ↦ yZ (κ.slot r)) (fun _ ↦ 1) (T.slotEquiv.symm e)

theorem mulVec_regrowCoords_int (y : Fin p → ℚ) (yZ : Fin p → ℤ) (hy : ∀ i, y i = yZ i) :
    (LengthMatrixPresentation.matrix
      (regrowTailed T hc hd J κ s).fullDim.labelling.presentation).mulVec
        (regrowCoords T hd J κ s y) =
      fun row ↦ (regrowRequestInt T J κ yZ row : ℚ) := by
  rw [show LengthMatrixPresentation.matrix
      (regrowTailed T hc hd J κ s).fullDim.labelling.presentation =
      (regrowTailed T hc hd J κ s).matrix from rfl, mulVec_regrowCoords]
  funext row
  obtain ⟨z, rfl⟩ := T.slotEquiv.surjective row
  rcases z with r | ⟨j, t⟩
  · rw [show T.slotEquiv (Sum.inl r) = T.coreSlot r from rfl, slot_coreSlot,
      Tailed.request_coreSlot, hy]
    simp [regrowRequestInt, Tailed.coreSlot]
  · rw [show T.slotEquiv (Sum.inr ⟨j, t⟩) = T.tailSlot j t from rfl, slot_tailSlot,
      Tailed.request_tailSlot]
    simp [regrowRequestInt, Tailed.tailSlot]

/-! ## 3.  The multiplicity -/

/-- **The tail factor is `1`**, read on the regrowth: `|Mult f| = |Mult(κ; marks)|`. -/
theorem absMult_regrowTailed : (regrowTailed T hc hd J κ s).absMult = κ.typedAbsMult := by
  have h := mult_tailedClassEquiv T hc hd (FrameClass.mk (regrowTailed T hc hd J κ s))
  rw [tailedClassEquiv_mk, restrictTailed_regrowTailed] at h
  exact h.symm

/-- Odd typed multiplicity of `κ` makes the natural multiplicity of `f` odd. -/
theorem odd_fdAbsMultNat (hOdd : ∃ m : ℕ, Odd m ∧ κ.typedAbsMult = m) :
    Odd (fdAbsMultNat (regrowTailed T hc hd J κ s).fullDim) := by
  obtain ⟨m, hm, hmem⟩ := hOdd
  have h : (fdAbsMultNat (regrowTailed T hc hd J κ s).fullDim : ℚ) = m := by
    rw [← fdAbsMult_eq_fdAbsMultNat, ← hmem, ← absMult_regrowTailed T hc hd J κ s]
    rfl
  have h' : fdAbsMultNat (regrowTailed T hc hd J κ s).fullDim = m := by exact_mod_cast h
  rw [h']
  exact hm

/-! ## 4.  The leaf columns -/

/-- An old vertex that is a leaf of the regrown target, and meets an old edge, is a leaf of the
old target. -/
theorem isLeafVertex_of_oldV {T₀ : CFGraph.{0}} {x : Fin k → T₀.V} {v : T₀.V}
    (hLeaf : IsLeafVertex (catTarget c T₀ x) (oldV c x v)) {ε : T₀.edges}
    (hε : ε ∈ incidentEdges v) : IsLeafVertex T₀ v := by
  unfold IsLeafVertex at hLeaf ⊢
  have h := card_incidentEdges_oldV c x v
  have hpos : 0 < (incidentEdges v).card := Finset.card_pos.mpr ⟨ε, hε⟩
  omega

/-- A core column that is a leaf column of `f` is a leaf column of `κ`. -/
theorem mem_leafColumns_of_coreSlot (i : Fin p)
    (h : T.coreSlot i ∈ leafColumns (regrowTailed T hc hd J κ s).fullDim.labelling.presentation) :
    i ∈ leafColumns κ.fullDim.labelling.presentation := by
  rw [mem_leafColumns] at h ⊢
  obtain ⟨v, hLeaf, hInc⟩ := h
  change (regrowTailed T hc hd J κ s).fullDim.labelling.targetEdge (T.coreSlot i) ∈ _ at hInc
  rw [targetEdge_coreSlot] at hInc
  have hInc' := fst_eq_or_snd_eq_of_mem_incidentEdges hInc
  rw [oldE_ends] at hInc'
  have hmem : κ.fullDim.labelling.targetEdge i ∈
      incidentEdges (κ.fullDim.labelling.targetEdge i : κ.target.V × κ.target.V).1 ∧
      κ.fullDim.labelling.targetEdge i ∈
      incidentEdges (κ.fullDim.labelling.targetEdge i : κ.target.V × κ.target.V).2 := by
    constructor <;> (rw [GluingDatum.incidentEdges, Finset.mem_filter]; simp)
  rcases hInc' with hv | hv
  · subst hv
    exact ⟨_, isLeafVertex_of_oldV hLeaf hmem.1, hmem.1⟩
  · subst hv
    exact ⟨_, isLeafVertex_of_oldV hLeaf hmem.2, hmem.2⟩

/-! ## 5.  The odd denominators -/

include T hc hd s in
/-- **Odd typed multiplicity gives odd denominators** to every leaf-adjusted coordinate of `κ`
at an integral request, through the regrowth: `OddDenominator.odd_leafAdjustedCoords_den` on
`f` at `T.request y`, read on the core columns. A leaf of `κ.target` that is not a leaf of
`f.target` (the image of a mark, when `κ` folds there) has its coordinate undoubled on `f`, and
doubling keeps the denominator odd. -/
theorem odd_leafAdjustedCoords_den_of_regrow (y : Fin p → ℚ) (yZ : Fin p → ℤ)
    (hy : ∀ i, y i = yZ i) (hOdd : ∃ m : ℕ, Odd m ∧ κ.typedAbsMult = m) (i : Fin p) :
    Odd (OddDenominator.leafAdjustedCoords κ.fullDim.labelling.presentation
      (κ.coordsAt y) i).den := by
  classical
  have hF := OddDenominator.odd_leafAdjustedCoords_den (regrowTailed T hc hd J κ s).fullDim
    (regrowRequestInt T J κ yZ) (regrowCoords T hd J κ s y)
    (mulVec_regrowCoords_int T hc hd J κ s y yZ hy) (odd_fdAbsMultNat T hc hd J κ s hOdd)
    (T.coreSlot i)
  rw [← mem_oddDenominatorSubring] at hF ⊢
  unfold OddDenominator.leafAdjustedCoords at hF ⊢
  rw [regrowCoords_coreSlot] at hF
  by_cases hκ : i ∈ leafColumns κ.fullDim.labelling.presentation
  · rw [ite_eq_left hκ]
    split_ifs at hF with hf
    · exact hF
    · exact oddDenominatorSubring.mul_mem (by exact_mod_cast natCast_mem oddDenominatorSubring 2) hF
  · rw [ite_eq_right hκ]
    have hf : T.coreSlot i ∉
        leafColumns (regrowTailed T hc hd J κ s).fullDim.labelling.presentation :=
      fun h ↦ hκ (mem_leafColumns_of_coreSlot T hc hd J κ s i h)
    rw [ite_eq_right hf] at hF
    exact hF

end DiagonalSecant.CM
