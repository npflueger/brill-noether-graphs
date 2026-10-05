module

public import DraismaVargasCount.Fibre

@[expose] public section

/-!
# Non-vacuity of the labelled fibre: the caterpillar of loops

**Source.**  Vargas, Part II (arXiv:2609.09109),
`lm:combinatorial-structure-caterpillar-of-loops` and the caterpillar step of
the proof of the main theorem (section
`sec-proof-main-theorems`).  This file is the **required non-vacuity witness**
for `DraismaVargasCount.Fibre`: the structures `CoreIdentification` and
`FibreMember` are inhabited here, uniformly in the genus `g = 2m + 2` and in the
requested lengths.

## What is proved

* `branchEquiv` -- **the branch vertices of the stable caterpillar are the
  `2g - 2` non-leaf vertices of `T^CL_g`**.  Every source vertex of surviving
  valency at least three is a central representative `coreVertex m v`
  (`eq_coreVertex_of_branch`, from `CaterpillarValency`'s census), the folded
  lollipop tips `v_i` have surviving valency exactly two, and every other
  non-leaf vertex has surviving valency exactly three.  The indexing
  `branchIdx v = 2v/3` is a bijection onto `Fin (4m+2)`.
* `incidenceCount_coreVertex` -- **the incidence census**: at a central vertex
  the surviving occurrences of the stable row `slot` are exactly the visible
  occurrences over the target occurrence `slot` -- two folded loop flags over a
  leaf edge, one bridge or spine occurrence otherwise, none when the target
  occurrence is not incident.  Proved by an explicit bijection
  (`Finset.card_bij`) from `CaterpillarValency.nonDanglingIncident_core_eq_visible`.
* `catCore` -- **the stable core of the caterpillar of loops**: `2g - 2`
  vertices, `3g - 3` slots, and `g` **self-loops** (the folded leaf rows have
  equal ends), with `coreIncidence_catCore` matching the census slot by slot.
* `catIdent` -- the `CoreIdentification`, whose row map is
  `CaterpillarRows.rowEquiv` (a stable row is the target occurrence it lies
  over).
* `catDiag_eq`, `catCoords_eq`, `catRealizes` -- **the realization equation as an
  explicit diagonal solve**: `CaterpillarRows.diagonalPattern` makes the length
  matrix diagonal, `Count.Caterpillar.matrix_diag_cat` gives its entries (`2` on
  a leaf edge, `1/2` on a pair edge, `1` on a slope-one spine edge), so
  `z_t = y_t / A_tt`.
* `caterpillarMember` -- **the member**, for every `m` and every request; it is
  `Open` for a positive request, `Closed` for a nonnegative one, and has
  `absMult = 1` (`Count.Caterpillar.fdAbsMult_caterpillar`), hence
  `HasOddMult`.  `exists_open_hasOddMult` is the headline.

## Scope

* Nothing here is a *count*: this is one member, not the fibre.  The other
  members over the same request are the ballot members of
  `BallotCoreIdentification`, and `CaterpillarAllMembers.cls_eq_ballot_genusSix`
  shows that at genus six every member lies in a ballot class.
* Oddness is the existential `HasOddMult` of `DraismaVargasCount.Fibre`; here it
  is discharged by the *value* `absMult = 1`, not by integrality of the
  multiplicity (which `DraismaVargasCount.Integrality`, downstream of this file,
  proves).
* The caterpillar core is **not** a `SubdivisionGraph.Spec.core`: `Spec` demands
  `core_loopless`, and `catCore` has `g` self-loops.  This is why
  `FibreMember` is indexed by a bare `ExplicitPotential.Core` together with a
  rational length vector rather than by a `Spec`.

## Consumers

The base count over the caterpillar of loops (step 1 of
`DraismaVargasCount/Assembly.lean`, over `catCore 2`) starts from `catCore` and
`caterpillarMember`; the ballot members of `BallotCoreIdentification` are
further members over the same core, built in the same way.
-/

namespace DraismaVargas.Count.FibreCaterpillar

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.LocalCases.CaterpillarSpine
open DraismaVargas.LocalCases.CaterpillarValency
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount incidentEdges mem_incidentEdges)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  The branch vertices of the stable caterpillar -/

/-- The core-vertex index of a non-leaf target vertex. -/
def branchIdx (vertex : ℕ) : ℕ := 2 * vertex / 3

/-- Its inverse on non-leaf target vertices. -/
def branchVal (index : ℕ) : ℕ := (3 * index + 1) / 2

theorem branchIdx_branchVal (index : ℕ) : branchIdx (branchVal index) = index := by
  unfold branchIdx branchVal; omega

theorem branchVal_branchIdx {vertex : ℕ} (hvertex : vertex % 3 ≠ 1) :
    branchVal (branchIdx vertex) = vertex := by
  unfold branchIdx branchVal; omega

theorem branchIdx_lt {m vertex : ℕ} (hvertex : vertex ≤ 6 * m + 2) :
    branchIdx vertex < 4 * m + 2 := by
  unfold branchIdx; omega

theorem branchVal_le (m : ℕ) {index : ℕ} (hindex : index < 4 * m + 2) :
    branchVal index ≤ 6 * m + 2 := by
  unfold branchVal; omega

theorem branchVal_mod (index : ℕ) : branchVal index % 3 ≠ 1 := by
  unfold branchVal; omega

theorem branchIdx_inj {a b : ℕ} (ha : a % 3 ≠ 1) (hb : b % 3 ≠ 1) :
    branchIdx a = branchIdx b ↔ a = b := by
  unfold branchIdx; omega

/-- A target vertex of `T^CL_g` that survives as a branch of the stable source:
everything except the `g` folded lollipop tips `v_i`. -/
def IsBranchIndex (m : ℕ) (vertex : (catTree m).V) : Prop :=
  vertex.val % 3 ≠ 1 ∧ vertex.val ≠ 6 * m + 3

instance (m : ℕ) (vertex : (catTree m).V) : Decidable (IsBranchIndex m vertex) := by
  unfold IsBranchIndex; infer_instance

theorem isBranchIndex_le {m : ℕ} {vertex : (catTree m).V}
    (hBranch : IsBranchIndex m vertex) : vertex.val ≤ 6 * m + 2 := by
  have hlt := vertex.isLt
  have hne := hBranch.2
  omega

/-- **Branches have surviving valency three.** -/
theorem nonDanglingValency_branch (m : ℕ) {vertex : (catTree m).V}
    (hBranch : IsBranchIndex m vertex) :
    nonDanglingValency (caterpillarDatum m) (coreVertex m vertex) = 3 := by
  rcases vertexClass m vertex with hRoot | hLeaf | hStem | hLastLeaf |
      hJunction | hLastStem
  · rw [show vertex = rootTarget m from Fin.ext hRoot,
      nonDanglingValency_core_root]
  · exact absurd hLeaf hBranch.1
  · rw [nonDanglingValency_core_stem vertex hStem.1 hStem.2.1 hStem.2.2]
  · exact absurd hLastLeaf hBranch.2
  · rw [nonDanglingValency_core_junction vertex hJunction.1 hJunction.2]
  · rw [nonDanglingValency_core_lastStem vertex hLastStem]

/-- **The folded tips have surviving valency two.** -/
theorem nonDanglingValency_not_branch (m : ℕ) {vertex : (catTree m).V}
    (hBranch : ¬ IsBranchIndex m vertex) :
    nonDanglingValency (caterpillarDatum m) (coreVertex m vertex) = 2 := by
  unfold IsBranchIndex at hBranch
  rw [not_and_or, not_ne_iff, not_ne_iff] at hBranch
  rcases hBranch with hLeaf | hLastLeaf
  · exact nonDanglingValency_core_leaf vertex hLeaf
  · exact nonDanglingValency_core_lastLeaf vertex hLastLeaf

/-- **Every branch vertex of the stable caterpillar is a central representative
over a non-leaf target vertex.** -/
theorem eq_coreVertex_of_branch {m : ℕ} {x : (caterpillarDatum m).SourceVertex}
    (hValency : 3 ≤ nonDanglingValency (caterpillarDatum m) x) :
    x = coreVertex m x.1.1 ∧ IsBranchIndex m x.1.1 := by
  have hCore : x = coreVertex m x.1.1 := by
    rcases sourceVertex_eq_core_or_other m x with hCore | hOther
    · exact hCore
    · exfalso
      have hSelf := (caterpillarDatum m).sourceEndpoint_self x
      rw [← hSelf, nonDanglingValency_sourceEndpoint_other_eq_zero m x.1.1 x.1.2
        hOther.1 hOther.2] at hValency
      omega
  refine ⟨hCore, ?_⟩
  by_contra hBranch
  rw [hCore, nonDanglingValency_not_branch m hBranch] at hValency
  omega

theorem coreVertex_fst (m : ℕ) (vertex : (catTree m).V) :
    (coreVertex m vertex).1.1 = vertex := rfl

/-- The non-leaf target vertex carrying the core vertex `index`. -/
def branchVertexOf (m : ℕ) (index : Fin (4 * m + 2)) : (catTree m).V :=
  ⟨branchVal index.val, by have := branchVal_le m index.isLt; omega⟩

@[simp] theorem branchVertexOf_val (m : ℕ) (index : Fin (4 * m + 2)) :
    (branchVertexOf m index).val = branchVal index.val := rfl

theorem isBranchIndex_branchVertexOf (m : ℕ) (index : Fin (4 * m + 2)) :
    IsBranchIndex m (branchVertexOf m index) := by
  refine ⟨?_, ?_⟩
  · rw [branchVertexOf_val]; exact branchVal_mod index.val
  · rw [branchVertexOf_val]
    have := branchVal_le m index.isLt
    omega

/-- The core index of a branch vertex. -/
noncomputable def branchIndexOf (m : ℕ) (branch : BranchVertex (caterpillarDatum m)) :
    Fin (4 * m + 2) :=
  ⟨branchIdx branch.1.1.1.val,
    branchIdx_lt (isBranchIndex_le (eq_coreVertex_of_branch branch.2).2)⟩

/-- **The branch vertices of the stable caterpillar, indexed by `Fin (2g-2)`.** -/
noncomputable def branchEquiv (m : ℕ) :
    BranchVertex (caterpillarDatum m) ≃ Fin (4 * m + 2) where
  toFun := branchIndexOf m
  invFun index := ⟨coreVertex m (branchVertexOf m index),
    (nonDanglingValency_branch m (isBranchIndex_branchVertexOf m index)).ge⟩
  left_inv branch := by
    obtain ⟨hCore, hBranch⟩ := eq_coreVertex_of_branch branch.2
    have hvertex : branchVertexOf m (branchIndexOf m branch) = branch.1.1.1 :=
      Fin.ext (branchVal_branchIdx hBranch.1)
    refine Subtype.ext ?_
    show coreVertex m (branchVertexOf m (branchIndexOf m branch)) = branch.1
    rw [hvertex]
    exact hCore.symm
  right_inv index := Fin.ext (branchIdx_branchVal index.val)

@[simp] theorem branchEquiv_apply (m : ℕ) (branch : BranchVertex (caterpillarDatum m)) :
    (branchEquiv m branch).val = branchIdx branch.1.1.1.val := rfl

@[simp] theorem branchEquiv_symm_apply (m : ℕ) (index : Fin (4 * m + 2)) :
    ((branchEquiv m).symm index).1 = coreVertex m (branchVertexOf m index) := rfl

/-! ## 2.  The incidences of the stable caterpillar -/

/-- **The complete incidence census of the stable caterpillar of loops.**  At a
central source vertex the surviving occurrences of the stable row `slot` are the
visible occurrences over the target occurrence `slot`: two folded loop flags over
a leaf edge, one bridge or spine occurrence otherwise, and none at all when the
target occurrence is not incident. -/
theorem incidenceCount_coreVertex (m : ℕ) (vertex : (catTree m).V)
    (slot : Fin (6 * m + 3)) :
    incidenceCount (caterpillarDatum m) (coreVertex m vertex)
        ((CaterpillarRows.rowEquiv m).symm slot) =
      if slot ∈ incidentIndices m vertex then
        (if IsLeafEdge m slot then 2 else 1) else 0 := by
  classical
  have hStar := nonDanglingIncident_core_eq_visible m vertex
  have hCard : ((incidentEdges (caterpillarDatum m) (coreVertex m vertex)).filter
      fun edge ↦ edge.stablePath = (CaterpillarRows.main m slot).stablePath).card =
      (if slot ∈ incidentIndices m vertex then visibleOccurrences m slot
        else (∅ : Finset (caterpillarDatum m).SourceEdge)).card := by
    refine Finset.card_bij (fun edge _ ↦ edge.1) ?_ ?_ ?_
    · intro edge hEdge
      rw [Finset.mem_filter, mem_incidentEdges] at hEdge
      have hMem : edge.1 ∈ nonDanglingIncident (caterpillarDatum m)
          (coreVertex m vertex) :=
        (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
      rw [hStar] at hMem
      obtain ⟨index, hIndex, hVisible⟩ := Finset.mem_biUnion.mp hMem
      have hTarget := sourceEdge_target_eq_occ_of_mem_visibleOccurrences hVisible
      have hRow : edge.stablePath = (CaterpillarRows.main m index).stablePath := by
        have hSymm : (catEdgeEquiv m).symm (occ m index) = index :=
          (catEdgeEquiv m).symm_apply_eq.mpr rfl
        rw [CaterpillarRows.edge_stablePath_eq_main m edge, hTarget, hSymm]
      have hEq : index = slot := by
        have hPath := hRow.symm.trans hEdge.2
        have hIndexEq := congrArg (CaterpillarRows.rowIndex m) hPath
        rwa [CaterpillarRows.rowIndex_main, CaterpillarRows.rowIndex_main] at hIndexEq
      subst hEq
      rw [ite_eq_left hIndex]
      exact hVisible
    · intro first _ second _ hEq
      exact Subtype.ext hEq
    · intro occurrence hOccurrence
      by_cases hIndex : slot ∈ incidentIndices m vertex
      · rw [ite_eq_left hIndex] at hOccurrence
        have hMem : occurrence ∈ nonDanglingIncident (caterpillarDatum m)
            (coreVertex m vertex) := by
          rw [hStar]
          exact Finset.mem_biUnion.mpr ⟨slot, hIndex, hOccurrence⟩
        obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
        have hSymm : (catEdgeEquiv m).symm (occ m slot) = slot :=
          (catEdgeEquiv m).symm_apply_eq.mpr rfl
        refine ⟨⟨occurrence, hSurvives⟩, Finset.mem_filter.mpr
          ⟨(mem_incidentEdges _ _ _).mpr hIncident, ?_⟩, rfl⟩
        rw [CaterpillarRows.edge_stablePath_eq_main m ⟨occurrence, hSurvives⟩,
          show ((⟨occurrence, hSurvives⟩ :
            NonDanglingEdge (caterpillarDatum m)) : (caterpillarDatum m).SourceEdge).1.1
              = occ m slot from
            sourceEdge_target_eq_occ_of_mem_visibleOccurrences hOccurrence, hSymm]
      · rw [ite_eq_right hIndex] at hOccurrence
        exact absurd hOccurrence (by simp)
  rw [incidenceCount, show (CaterpillarRows.rowEquiv m).symm slot =
      (CaterpillarRows.main m slot).stablePath from rfl, hCard]
  by_cases hIndex : slot ∈ incidentIndices m vertex
  · rw [ite_eq_left hIndex, ite_eq_left hIndex, card_visibleOccurrences]
  · rw [ite_eq_right hIndex, ite_eq_right hIndex, Finset.card_empty]

/-! ## 3.  The core of the caterpillar of loops -/

/-- The target vertex carrying the tail of the stable row `slot`: the parent of
the target occurrence.  Every stable row has this end. -/
def catTailVal (m : ℕ) (slot : Fin (6 * m + 3)) : ℕ := parentIndex (slot.val + 1)

/-- The target vertex carrying the head of the stable row `slot`.  Over a leaf
edge the row is the folded loop, and its head is its tail: **the stable core of
the caterpillar of loops has `g` self-loops**. -/
def catHeadVal (m : ℕ) (slot : Fin (6 * m + 3)) : ℕ :=
  if IsLeafEdge m slot then parentIndex (slot.val + 1) else slot.val + 1

theorem catTailVal_le (m : ℕ) (slot : Fin (6 * m + 3)) :
    catTailVal m slot ≤ 6 * m + 2 := by
  have hlt := slot.isLt
  have := parentIndex_le_pred (slot.val + 1)
  unfold catTailVal
  omega

theorem catTailVal_mod (m : ℕ) (slot : Fin (6 * m + 3)) :
    catTailVal m slot % 3 ≠ 1 := by
  unfold catTailVal parentIndex
  split_ifs <;> omega

theorem catHeadVal_le (m : ℕ) (slot : Fin (6 * m + 3)) :
    catHeadVal m slot ≤ 6 * m + 2 := by
  have hlt := slot.isLt
  have hparent := parentIndex_le_pred (slot.val + 1)
  by_cases hLeaf : IsLeafEdge m slot
  · rw [catHeadVal, ite_eq_left hLeaf]
    omega
  · rw [catHeadVal, ite_eq_right hLeaf]
    unfold IsLeafEdge at hLeaf
    rw [not_or] at hLeaf
    omega

theorem catHeadVal_mod (m : ℕ) (slot : Fin (6 * m + 3)) :
    catHeadVal m slot % 3 ≠ 1 := by
  have hlt := slot.isLt
  by_cases hLeaf : IsLeafEdge m slot
  · rw [catHeadVal, ite_eq_left hLeaf]
    exact catTailVal_mod m slot
  · rw [catHeadVal, ite_eq_right hLeaf]
    unfold IsLeafEdge at hLeaf
    rw [not_or] at hLeaf
    omega

/-- **The stable core of the caterpillar of loops**, `g = 2m + 2` self-loops on a
spine: `2g - 2` vertices, `3g - 3` slots.  It is *not* loopless, so it is not a
`SubdivisionGraph.Spec.core`. -/
def catCore (m : ℕ) : Core (4 * m + 2) (6 * m + 3) where
  tail slot := ⟨branchIdx (catTailVal m slot), branchIdx_lt (catTailVal_le m slot)⟩
  head slot := ⟨branchIdx (catHeadVal m slot), branchIdx_lt (catHeadVal_le m slot)⟩

/-- **The core matches the incidence census.** -/
theorem coreIncidence_catCore (m : ℕ) {vertex : (catTree m).V}
    (hBranch : IsBranchIndex m vertex) (index : Fin (4 * m + 2))
    (hIndex : index.val = branchIdx vertex.val) (slot : Fin (6 * m + 3)) :
    coreIncidence (catCore m) index slot =
      if slot ∈ incidentIndices m vertex then
        (if IsLeafEdge m slot then 2 else 1) else 0 := by
  have hlt := slot.isLt
  have hvlt := vertex.isLt
  have hparent := parentIndex_le_pred (slot.val + 1)
  have hTail : ((catCore m).tail slot = index) ↔ catTailVal m slot = vertex.val := by
    rw [Fin.ext_iff]
    change branchIdx (catTailVal m slot) = index.val ↔ _
    rw [hIndex, branchIdx_inj (catTailVal_mod m slot) hBranch.1]
  have hHead : ((catCore m).head slot = index) ↔ catHeadVal m slot = vertex.val := by
    rw [Fin.ext_iff]
    change branchIdx (catHeadVal m slot) = index.val ↔ _
    rw [hIndex, branchIdx_inj (catHeadVal_mod m slot) hBranch.1]
  obtain ⟨hMod, hLast⟩ := hBranch
  rw [coreIncidence]
  simp only [hTail, hHead, mem_incidentIndices]
  unfold catHeadVal
  by_cases hLeaf : IsLeafEdge m slot
  · rw [ite_eq_left hLeaf, ite_eq_left hLeaf]
    unfold catTailVal parentIndex
    unfold IsLeafEdge at hLeaf
    split_ifs <;> omega
  · rw [ite_eq_right hLeaf, ite_eq_right hLeaf]
    unfold catTailVal parentIndex
    unfold IsLeafEdge at hLeaf
    rw [not_or] at hLeaf
    split_ifs <;> omega

/-! ## 4.  The identification of the stable caterpillar with its core -/

/-- **The label.**  The stable graph of the caterpillar gluing datum *is* the
caterpillar of loops `catCore m`, with the stable rows numbered by the target
occurrences they lie over (`CaterpillarRows.rowEquiv`). -/
noncomputable def catIdent (m : ℕ) :
    CoreIdentification (catCore m) (caterpillarDatum m) where
  vertex := branchEquiv m
  row := CaterpillarRows.rowEquiv m
  incidence branch slot := by
    obtain ⟨hCore, hBranch⟩ := eq_coreVertex_of_branch branch.2
    rw [show branch.1 = coreVertex m branch.1.1.1 from hCore,
      incidenceCount_coreVertex m branch.1.1.1 slot,
      coreIncidence_catCore m hBranch (branchEquiv m branch) rfl slot]

/-! ## 5.  The diagonal solve -/

/-- The diagonal entry of the caterpillar length matrix on the row `slot`. -/
noncomputable def catDiag (m : ℕ) (slot : Fin (6 * m + 3)) : ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (CaterpillarRows.labelling m).presentation slot slot

/-- `Count.Caterpillar.matrix_diag_cat`, read as the diagonal of the solve: `2`
on a leaf edge, `1/2` on a pair edge, `1` on a slope-one spine edge. -/
theorem catDiag_eq (m : ℕ) (slot : Fin (6 * m + 3)) :
    catDiag m slot =
      if IsLeafEdge m slot then 2 else if IsPairEdge m slot.val then 1 / 2 else 1 :=
  Caterpillar.matrix_diag_cat m slot

theorem catDiag_pos (m : ℕ) (slot : Fin (6 * m + 3)) : 0 < catDiag m slot :=
  (CaterpillarRows.diagonalPattern m).matrix_diag_pos slot

theorem catDiag_ne_zero (m : ℕ) (slot : Fin (6 * m + 3)) : catDiag m slot ≠ 0 :=
  (catDiag_pos m slot).ne'

/-- **The coordinate vector**: the caterpillar length matrix is diagonal, so the
realization equation is solved entry by entry. -/
noncomputable def catCoords (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (slot : Fin (6 * m + 3)) : ℚ :=
  request slot / catDiag m slot

/-- The explicit solve, with the diagonal spelled out. -/
theorem catCoords_eq (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (slot : Fin (6 * m + 3)) :
    catCoords m request slot = request slot /
      (if IsLeafEdge m slot then 2 else if IsPairEdge m slot.val then 1 / 2 else 1) := by
  rw [catCoords, catDiag_eq]

theorem catCoords_pos {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) (slot : Fin (6 * m + 3)) :
    0 < catCoords m request slot :=
  div_pos (hRequest slot) (catDiag_pos m slot)

theorem catCoords_nonneg {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 ≤ request slot) (slot : Fin (6 * m + 3)) :
    0 ≤ catCoords m request slot :=
  div_nonneg (hRequest slot) (catDiag_pos m slot).le

/-- **The realization equation, as an explicit diagonal solve.** -/
theorem catRealizes (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (GluingDatum.LengthMatrixPresentation.matrix
        (CaterpillarRows.labelling m).presentation).mulVec (catCoords m request) =
      fun row ↦ request ((CaterpillarRows.rowEquiv m)
        ((CaterpillarRows.labelling m).row.symm row)) := by
  funext row
  rw [(CaterpillarRows.diagonalPattern m).matrix_eq_diagonal, Matrix.mulVec_diagonal]
  show catDiag m row * catCoords m request row =
    request ((CaterpillarRows.rowEquiv m) ((CaterpillarRows.rowEquiv m).symm row))
  rw [Equiv.apply_symm_apply, catCoords, mul_div_cancel₀ _ (catDiag_ne_zero m row)]

/-! ## 6.  The caterpillar member -/

/-- **Non-vacuity, uniformly in the genus `g = 2m + 2` and in the request.**
Over every positive length vector on the caterpillar-of-loops core, the
caterpillar gluing datum `caterpillarDatum m`, with its full-dimensional
presentation `CaterpillarRows.fullDim m`, is a member of the labelled fibre. -/
noncomputable def caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    FibreMember (catCore m) request (m + 2) where
  target := catTree m
  data := caterpillarDatum m
  fullDim := CaterpillarRows.fullDim m
  ident := catIdent m
  coords := catCoords m request
  realizes := catRealizes m request

@[simp] theorem caterpillarMember_coords (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).coords = catCoords m request := rfl

/-- The caterpillar member lies in the fibre proper whenever the request is. -/
theorem caterpillarMember_open {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) : (caterpillarMember m request).Open :=
  fun slot ↦ catCoords_pos hRequest slot

theorem caterpillarMember_closed {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 ≤ request slot) : (caterpillarMember m request).Closed :=
  fun slot ↦ catCoords_nonneg hRequest slot

/-- **The caterpillar member has multiplicity one**, hence odd multiplicity --
`Caterpillar.absMult_caterpillar`, uniformly in `m`. -/
theorem caterpillarMember_absMult (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).absMult = 1 :=
  Caterpillar.fdAbsMult_caterpillar m

theorem caterpillarMember_hasOddMult (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).HasOddMult :=
  FibreMember.hasOddMult_of_absMult_eq_one (caterpillarMember_absMult m request)

/-- **The headline non-vacuity statement.**  Over every metric caterpillar of
loops of genus `2m + 2` the labelled fibre has a member of the open cone with
odd multiplicity. -/
theorem exists_open_hasOddMult (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    ∃ member : FibreMember (catCore m) request (m + 2),
      member.Open ∧ member.HasOddMult :=
  ⟨caterpillarMember m request, caterpillarMember_open hRequest,
    caterpillarMember_hasOddMult m request⟩

/-- Its class is an odd class of the fibre. -/
theorem isOddClass_caterpillar (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    IsOddClass (caterpillarMember m request).cls :=
  isOddClass_cls_of_hasOddMult (caterpillarMember_hasOddMult m request)

/-! ## 7.  Concrete values -/

/-- Genus six (`m = 2`): the all-ones request on the fifteen slots of the
caterpillar of loops, its member, and the first coordinate of the solve -- the
leaf row `0` has diagonal entry `2`, so its coordinate is `1/2`. -/
example : ((caterpillarMember 2 (fun _ ↦ 1)).coords 0) = 1 / 2 := by
  rw [caterpillarMember_coords, catCoords_eq]
  norm_num [IsLeafEdge]

/-- The spine row `1` of the genus-six caterpillar is a pair edge, so its
coordinate is `2`. -/
example : ((caterpillarMember 2 (fun _ ↦ 1)).coords 1) = 2 := by
  rw [caterpillarMember_coords, catCoords_eq]
  norm_num [IsLeafEdge, IsPairEdge]

/-- Genus six: the member of the all-ones fibre, in the open cone, of
multiplicity one. -/
example : (caterpillarMember 2 (fun _ ↦ 1)).Open ∧
    (caterpillarMember 2 (fun _ ↦ 1)).absMult = 1 :=
  ⟨caterpillarMember_open (fun _ ↦ one_pos), caterpillarMember_absMult 2 _⟩

/-- Non-vacuity of `MemberIso` at a concrete member: the identity isomorphism of
the genus-six caterpillar member with itself. -/
example : IsoOverCore (caterpillarMember 2 (fun _ ↦ 1)) (caterpillarMember 2 (fun _ ↦ 1)) :=
  isoOverCore_refl _

/-- Non-vacuity of the quotient: the genus-six caterpillar class. -/
example : Fibre.Open (caterpillarMember 2 (fun _ ↦ 1)).cls :=
  caterpillarMember_open (fun _ ↦ one_pos)

end DraismaVargas.Count.FibreCaterpillar
