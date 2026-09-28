import DraismaVargas.LocalCases.CaterpillarValency
import DraismaVargas.LocalCases.CaterpillarStable
import DraismaVargas.LocalCases.SeedDeterminant

/-!
# Full-dimensional caterpillar: actual stable rows and diagonal determinant

This is the stable-source half of the alternating-slope seed of Vargas, Part II,
§3.3 (caterpillars of loops). The exact occurrence and vertex censuses imply
that stable paths never cross target occurrences; the two flags above a leaf are
consecutive at its fold. Thus the target occurrence beneath a surviving edge is
a well-defined bijection from actual stable rows to `Fin (6m+3)`. The central
occurrence supplies the inverse and proves every row nonempty.

The induced honest matrix is diagonal with positive entries, so
`SeedDeterminant.DiagonalPattern` gives its nonsingularity. Every row has a
non-divalent parent endpoint. `fullDim` consequently takes only `m`: no
pruning, stable-path, trivalence or determinant input.
-/

namespace DraismaVargas.LocalCases.CaterpillarRows

open DraismaVargas.Infrastructure CaterpillarTree
open CaterpillarDatum CaterpillarPruning CaterpillarSpine W4StableSource

theorem leaf_or_stem_or_spine (m : ℕ) (i : Fin (6 * m + 3)) :
    IsLeafEdge m i ∨ IsStemEdge m i ∨ IsSpineEdge i := by
  unfold IsLeafEdge IsStemEdge IsSpineEdge
  omega

theorem main_survives (m : ℕ) (i : Fin (6 * m + 3)) :
    ¬ IsDangling (caterpillarDatum m) ((caterpillarDatum m).sourceEdge (occ m i) 0) := by
  rcases leaf_or_stem_or_spine m i with hLeaf | hStem | hSpine
  · exact loopFirst_survives hLeaf
  · exact stemMain_survives hStem
  · exact spineMain_survives hSpine

noncomputable def main (m : ℕ) (i : Fin (6 * m + 3)) :
    NonDanglingEdge (caterpillarDatum m) :=
  ⟨(caterpillarDatum m).sourceEdge (occ m i) 0, main_survives m i⟩

/-- Every surviving block in one target fibre belongs to the central
occurrence's stable row. On a leaf these are the two consecutive loop flags;
on a bridge they are one and the same quotient-source occurrence. -/
theorem sourceEdge_stablePath_eq_main (m : ℕ) (i : Fin (6 * m + 3)) (s : Fin (m + 2))
    (hSurvives : ¬ IsDangling (caterpillarDatum m)
      ((caterpillarDatum m).sourceEdge (occ m i) s)) :
    NonDanglingEdge.stablePath (data := caterpillarDatum m)
      ⟨(caterpillarDatum m).sourceEdge (occ m i) s, hSurvives⟩ = (main m i).stablePath := by
  by_cases hs0 : s.val = 0
  · have hs : s = 0 := Fin.ext hs0
    subst s
    rfl
  rcases leaf_or_stem_or_spine m i with hLeaf | hStem | hSpine
  · have hs : s.val = (partnerSheet m i).val := by
      by_contra h
      exact hSurvives ((leafOccurrence_isDangling_iff hLeaf s).mpr ⟨hs0, h⟩)
    have hsFin : s = partnerSheet m i := Fin.ext hs
    subst s
    exact (stablePath_eq_of_consecutive (loopFlags_consecutive hLeaf)).symm
  · have hs : s.val = (partnerSheet m i).val := by
      by_contra h
      exact hSurvives ((stemOccurrence_isDangling_iff hStem s).mpr ⟨hs0, h⟩)
    have hEq : (caterpillarDatum m).sourceEdge (occ m i) s =
        (caterpillarDatum m).sourceEdge (occ m i) 0 := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      change ((caterpillarDatum m).edgePartition (occ m i)).Rel s 0
      rw [caterpillarDatum_edgePartition, catEdgePart_of_pair m i (pair_of_stem hStem)]
      exact pairPart_rel_zero m _ s hs
    exact congrArg (NonDanglingEdge.stablePath (data := caterpillarDatum m))
      (show (⟨_, hSurvives⟩ : NonDanglingEdge (caterpillarDatum m)) = main m i from
        Subtype.ext hEq)
  · have hi : i.val = 6 * (s.val - 1) + 1 := by
      by_contra h
      exact hSurvives ((spineOccurrence_isDangling_iff hSpine s).mpr ⟨hs0, h⟩)
    have hiFin : i = spineIndex m (localSpineQ m s) := by
      apply Fin.ext
      simp only [spineIndex_val, localSpineQ_val, localSpinePosition]
      omega
    subst i
    exact congrArg (NonDanglingEdge.stablePath (data := caterpillarDatum m))
      (show (⟨_, hSurvives⟩ : NonDanglingEdge (caterpillarDatum m)) =
          main m (spineIndex m (localSpineQ m s)) from
        Subtype.ext (localSpineOccurrence_eq_main s hs0))

theorem edge_stablePath_eq_main (m : ℕ) (edge : NonDanglingEdge (caterpillarDatum m)) :
    edge.stablePath = (main m ((catEdgeEquiv m).symm edge.1.1.1)).stablePath := by
  let i := (catEdgeEquiv m).symm edge.1.1.1
  have hi : occ m i = edge.1.1.1 := (catEdgeEquiv m).apply_symm_apply _
  have hEq : (caterpillarDatum m).sourceEdge (occ m i) edge.1.1.2 = edge.1 := by
    rw [hi]
    exact W4StableSource.GluingDatum.sourceEdge_self _ _
  have hs : ¬ IsDangling (caterpillarDatum m)
      ((caterpillarDatum m).sourceEdge (occ m i) edge.1.1.2) := hEq.symm ▸ edge.2
  exact (congrArg (NonDanglingEdge.stablePath (data := caterpillarDatum m))
    (show (⟨_, hs⟩ : NonDanglingEdge (caterpillarDatum m)) = edge from Subtype.ext hEq)).symm.trans
    (sourceEdge_stablePath_eq_main m i edge.1.1.2 hs)

section Rows

variable (m : ℕ)

/-- The stable-row coordinate is the target occurrence beneath it. -/
noncomputable def rowIndex : StablePath (caterpillarDatum m) → Fin (6 * m + 3) :=
  Quot.lift (fun edge : NonDanglingEdge (caterpillarDatum m) ↦
    (catEdgeEquiv m).symm edge.1.1.1)
    (fun first second h ↦ congrArg (catEdgeEquiv m).symm (CaterpillarValency.target_eq_of_consecutive first second h))

theorem rowIndex_main (i : Fin (6 * m + 3)) :
    rowIndex m (main m i).stablePath = i :=
  (catEdgeEquiv m).symm_apply_apply i

theorem main_rowIndex (row : StablePath (caterpillarDatum m)) :
    (main m (rowIndex m row)).stablePath = row := by
  induction row using Quot.inductionOn with
  | h edge => exact (edge_stablePath_eq_main m edge).symm

/-- Actual stable rows, not merely an equinumerous set of indices. -/
noncomputable def rowEquiv : StablePath (caterpillarDatum m) ≃ Fin (6 * m + 3) where
  toFun := rowIndex m
  invFun i := (main m i).stablePath
  left_inv := main_rowIndex m
  right_inv := rowIndex_main m

noncomputable def labelling :
    StableLengthMatrixLabelling (caterpillarDatum m) (Fin (6 * m + 3)) where
  targetEdge := catEdgeEquiv m
  row := rowEquiv m

/-- The honest row enumeration is diagonal and every row is nonempty.
The source paper's diagonal determinant argument therefore applies directly. -/
theorem diagonalPattern : SeedDeterminant.DiagonalPattern
    (labelling m).presentation where
  liesOver := by
    intro i edge hMem
    obtain ⟨hSurvives, hRow⟩ :=
      (StableLengthMatrixLabelling.mem_path_iff (labelling m) i edge).mp hMem
    change (catEdgeEquiv m).symm edge.1.1 = i at hRow
    apply (catEdgeEquiv m).symm.injective
    exact hRow.trans ((catEdgeEquiv m).symm_apply_apply i).symm
  pathNeNil := by
    intro i hEmpty
    have hMem : (main m i).1 ∈ (labelling m).path i := by
      apply (StableLengthMatrixLabelling.mem_path_iff _ _ _).mpr
      exact ⟨(main m i).2, rowIndex_main m i⟩
    rw [show (labelling m).path i = [] from hEmpty] at hMem
    exact List.not_mem_nil hMem

theorem det_pos : 0 < (GluingDatum.LengthMatrixPresentation.matrix
    (labelling m).presentation).det :=
  (diagonalPattern m).det_pos

theorem det_ne_zero : (GluingDatum.LengthMatrixPresentation.matrix
    (labelling m).presentation).det ≠ 0 :=
  (diagonalPattern m).det_ne_zero

end Rows

/-- Every chosen central occurrence has a non-divalent left endpoint: the
parent of a target edge is never one of the leaf folds. -/
theorem main_left_isPathEnd (m : ℕ) (i : Fin (6 * m + 3)) :
    IsPathEnd (caterpillarDatum m) (main m i).1 (coreVertex m (catParent m i)) := by
  constructor
  · change Incident (caterpillarDatum m)
      ((caterpillarDatum m).sourceEdge (occ m i) 0) (coreVertex m (catParent m i))
    unfold Incident
    rw [sourceEnds_sourceEdge]
    exact Or.inl rfl
  · intro hValency
    obtain ⟨j, hLeaf, hVertex⟩ :=
      CaterpillarValency.eq_foldVertex_of_nonDanglingValency_eq_two _ hValency
    have hTarget := congrArg (fun vertex : (caterpillarDatum m).SourceVertex ↦
      vertex.1.1.val) hVertex
    change parentIndex (i.val + 1) = j.val + 1 at hTarget
    have hi := i.isLt
    unfold IsLeafEdge at hLeaf
    unfold parentIndex at hTarget
    split_ifs at hTarget <;> omega

/-- Every actual stable row reaches a branch; the pruned source has no
cyclic stable-path component. -/
theorem hasPathEnds (m : ℕ) : HasPathEnds (caterpillarDatum m) := by
  intro edge
  let i := (catEdgeEquiv m).symm edge.1.1.1
  exact ⟨main m i, coreVertex m (catParent m i),
    (edge_stablePath_eq_main m edge).symm, main_left_isPathEnd m i⟩

/-- The complete source-facing Part II caterpillar presentation, uniformly
in genus `2m+2`, with no pruning, path, labelling or determinant inputs. -/
noncomputable def fullDim (m : ℕ) :
    FullDimensionalSource.FullDimensionalSourcePresentation
      (caterpillarDatum m) (Fin (6 * m + 3)) :=
  CaterpillarStable.presentationOfStableData m (labelling m) (det_ne_zero m)
    (CaterpillarValency.nonDanglingValency_le_three m) (hasPathEnds m)

end DraismaVargas.LocalCases.CaterpillarRows
