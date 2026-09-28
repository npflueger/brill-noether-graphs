import DraismaVargas.LocalCases.W3Nd3LimitMatrix
import Utilities.IntegralGeometry.WallColumnDeterminant

/-!
# Figure 30 common cofactors and Equation (4)

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t3}, Figure 30 and Equation
(4).  Figure 30 and the prose of the case attach the two members to `α = 3`
and `α = 4` in opposite ways; this module follows the figure.

`W3Nd3SourceCandidates` builds both Figure 30 members `M⁽¹⁾` (coarse) and
`M⁽²⁾` (fine) over **one** incoming datum; `W3Nd3StableGraph` supplies the
endpoint dictionary and survival; `W3Nd3LimitMatrix` proves the two honest
limit matrices — every retained column is literally the source's
(`coarse_matrix_retained`, `fine_matrix_retained`), and the two new columns
are `coarse_matrix_new_on_old_row` and `fine_matrix_new_on_old_row`.  This
module weights those columns by cofactors and turns the column identity into
the determinant identity, following `W3Nd2CommonBalance` and `W4CommonBalance`.

## The column identity, and why it is crossed

Write `t₃ = profile.first.1.1.1` for the doubled direction (`hSame` says `e₂`
and `e₃` share it), `t₄ = largestTarget input profile` for the largest
direction, and `k₂, k₃, k₄` for the three dilation indices.  The two old
columns decompose over the distinguished block as

* `doubled_matrix_decomposition` — the old `t₃` column carries **two** selected
  occurrences, `1/k₂` on `e₂`'s row and `1/k₃` on `e₃`'s row, plus the `t₃`
  background sum;
* `largest_matrix_decomposition` — the old `t₄` column carries the single
  selected occurrence `1/k₄` on `e₄`'s row, plus the `t₄` background sum.

`W3Nd3LimitMatrix`'s two new columns are neither of those.  `M⁽¹⁾`'s new column
is `1/(k₂ + k₃)` on `e₄`'s row plus the **old `t₃` background**, and `M⁽²⁾`'s
new column is `1/k₂` on `e₂`'s row and `1/k₃` on `e₃`'s row plus the **old `t₄`
background**.  So each member's new column carries the *other* old column's
selected part, and the identity that comes out — `new_columns_add_eq_old` — is

    coarse new column + fine new column = old `t₃` column + old `t₄` column

with the two sides matching only after `largest_index_cast`, i.e.
`k₄ = k₂ + k₃`, which `Nd3Profile.doubled_direction` derives from `hSame`.
This crossing is exactly the shape of `BalancingRemaining.balance_w3_nd3_t3`:
the coarse determinant is `c₄/(k₂+k₃) + s₃` and the fine one is
`c₂/k₂ + c₃/k₃ + s₄`, and their sum is the sum of the two vanishing old-column
contributions `c₂/k₂ + c₃/k₃ + s₃` and `c₄/(k₂+k₃) + s₄`.  Nothing here asserts
that `e₂`'s and `e₃`'s stable rows are distinct, and the formulas stay correct
if a stable loop makes them equal: the two selected terms are kept as separate
indicator terms throughout.

## What is proved

* `commonMatrix` — both members' natural stable-length matrices read in one
  coordinate system: incoming stable rows through `coarseStablePathEquiv` /
  `fineStablePathEquiv`, `Option target.edges` columns through
  `occurrenceEquiv`, with `none` the new wall column.  `commonMatrix_retained`
  and `commonMatrix_new_add` are the retained-column theorems and the crossed
  column identity in those coordinates.
* `matrices_agree`, `common_cofactors` — the two square matrices agree away
  from the wall column, from the retained columns alone, so the wall row of the
  adjugate is literally common to both.  No nonsingularity is assumed and no
  cofactor correspondence is supplied.
* `old_column_annihilation`, `determinant_balance` — **Equation (4)**:
  `det A⁽¹⁾ + det A⁽²⁾ = 0`.  Summing the column identity against the common
  cofactors turns the two determinants into the two old columns'
  cofactor-weighted contributions, each of which vanishes as an off-diagonal
  entry of `adjugate A * A = det A • 1`.  The two determinants enter with the
  **unit weights** `![1, 1]`, exactly as `balance_w3_nd3_t3` uses them; no
  general weights are needed, because `k₄ = k₂ + k₃` has already absorbed the
  only arithmetic.
* `family`, `honestPresentedFamily` — a `BalancedGlobal.Family` and a
  `BalancedGlobal.PresentedFamily 2 data wall` on the **same** `data`.  Both
  nd3 members live over one datum, so this needs no branch swap and no gauge
  family.  The matrices are the honest
  `GluingDatum.LengthMatrixPresentation.matrix` of a
  `StableLengthMatrixLabelling` on the real data
  (`family_matrix_is_honest`), not raw lists.
* `exists_valid_opposite`, `exists_valid_positive_exit_with_pencil` — the
  identified-member exit.  Only the **chosen incoming** member is assumed
  nonsingular; the other member may be singular and stays in the family.
* `canonicalRowOrder`, `canonicalMatrix`, `canonical_determinant_balance`,
  `canonicalFamily`, `canonicalPresentedFamily` — the same statements with the
  coordinate order forced by `input.stablePath_card`, so nothing external is
  supplied.

## Hypotheses

Exactly `W3Nd3LimitMatrix`'s: an actual `W3SourceInput data star`, an actual
`Nd3Profile data input.distinguishedBlock`, and `hSame`, the first alternative
of `W3R1SourceProfile.Nd3Profile.cases`.  No new hypothesis is added anywhere;
in particular no nonsingularity, no distinctness of the rows of `e₂` and `e₃`,
and no numerical assumption — `k₄ = k₂ + k₃` is derived.

## What is deliberately not here

`GlobalCoarseFine.nd3BalancedFamily` stays **unclaimed**, and this module does
not touch `GlobalCoarseFine.lean`.  That family requires
`TrivalentPattern … geometry.fineLocal`, whereas the actual Figure 30 fine
member uses `W3Nd3SourceCandidates.selectedResolution`, the
`LocalResolution.reverse` of `fineResolution`: `fineLocal` places the fine
partition at the **divalent** endpoint, which is not Figure 30's `M⁽²⁾`,
exactly as `W3Nd3SourceCandidates` records.  The family here is therefore built
directly from `BalancedGlobal.PresentedFamily`, which takes two `Candidate`s on
one datum and imposes no pattern requirement.

Also not here: identifying an *arbitrary* incoming nd3 datum with one of the
two members (`W3Nd3IncomingMatching`, modelled on
`W3Nd2IncomingMemberMatching`), and the original-coordinate restatement
(`W3Nd3GraphTracking`).
-/

namespace DraismaVargas.LocalCases.W3Nd3CommonBalance

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource ThirdEquation StableSourceMatrix
open W3R1SourceProfile W3Nd3SourceCandidates W3Nd3StableGraph
open W3Nd3LimitMatrix

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  (input : W3SourceInput data star)
  (profile : Nd3Profile data input.distinguishedBlock)

private theorem selected_doubled_eq {path : StablePath data} (edge : data.SourceEdge)
    (hMem : edge ∈ occurrences data path profile.first.1.1.1)
    (hRel : (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2) :
    edge = profile.first.1 ∨ edge = profile.second.1 := by
  obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
  have hIncident : Incident data edge
      (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
    apply (incident_iff_target_mem_and_rel data edge _).mpr
    refine ⟨hTarget ▸ incident_target_mem input profile.first, ?_⟩
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr input.distinguishedBlock.1) edge.1.2
    exact ((data.vertexPartition wall).rel_repr_left input.distinguishedBlock.1).trans hRel
  rcases selected_survivor_cases input profile ⟨edge, hSurvives⟩ hIncident with
      hFirst | hSecond | hLargest
  · exact Or.inl hFirst
  · exact Or.inr hSecond
  · have hLargestTarget := congrArg (fun e : data.SourceEdge ↦ e.1.1) hLargest
    exact (profile.first_target_ne (hTarget.symm.trans hLargestTarget)).elim

private theorem selected_largest_eq {path : StablePath data} (edge : data.SourceEdge)
    (hMem : edge ∈ occurrences data path (largestTarget input profile))
    (hRel : (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2) :
    edge = profile.largest.1 := by
  obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
  have hIncident : Incident data edge
      (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
    apply (incident_iff_target_mem_and_rel data edge _).mpr
    refine ⟨hTarget ▸ incident_target_mem input profile.largest, ?_⟩
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr input.distinguishedBlock.1) edge.1.2
    exact ((data.vertexPartition wall).rel_repr_left input.distinguishedBlock.1).trans hRel
  rcases selected_survivor_cases input profile ⟨edge, hSurvives⟩ hIncident with
      hFirst | hSecond | hLargest
  · have hFirstTarget := congrArg (fun e : data.SourceEdge ↦ e.1.1) hFirst
    exact (profile.first_target_ne (hFirstTarget.symm.trans hTarget)).elim
  · have hSecondTarget := congrArg (fun e : data.SourceEdge ↦ e.1.1) hSecond
    exact (profile.second_target_ne (hSecondTarget.symm.trans hTarget)).elim
  · exact hLargest

/-- The old doubled-direction column `t₃` consists of its **two** selected
occurrences `e₂`, `e₃` and all literal background occurrences. -/
theorem doubled_matrix_decomposition
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (path : StablePath data) :
    matrix data path profile.first.1.1.1 =
      (if path = NonDanglingEdge.stablePath
          ⟨profile.first.1, first_survives input profile⟩ then
        (1 : ℚ) / data.sourceEdgeIndex profile.first.1 else 0) +
      (if path = NonDanglingEdge.stablePath
          ⟨profile.second.1, second_survives input profile⟩ then
        (1 : ℚ) / data.sourceEdgeIndex profile.second.1 else 0) +
      ∑ edge ∈ coarseOldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  let selected := (occurrences data path profile.first.1.1.1).filter
    (fun edge ↦ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2)
  have hSelected : selected =
      ({profile.first.1, profile.second.1} : Finset data.SourceEdge).filter
        (fun edge ↦ edge ∈ occurrences data path profile.first.1.1.1) := by
    ext edge
    simp only [selected, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hMem, hRel⟩
      exact ⟨selected_doubled_eq input profile edge hMem hRel, hMem⟩
    · rintro ⟨hEq, hMem⟩
      refine ⟨hMem, ?_⟩
      rcases hEq with rfl | rfl
      · exact incident_wall_rel input profile.first
      · exact incident_wall_rel input profile.second
  have hMem (edge : NonDanglingEdge data)
      (hTarget : edge.1.1.1 = profile.first.1.1.1) :
      edge.1 ∈ occurrences data path profile.first.1.1.1 ↔
        path = edge.stablePath := by
    rw [mem_occurrences]
    exact ⟨fun h ↦ h.1.choose_spec.symm, fun h ↦ ⟨⟨edge.2, h.symm⟩, hTarget⟩⟩
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (occurrences data path profile.first.1.1.1)
    (fun edge ↦ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2)
    (fun edge ↦ (1 : ℚ) / data.sourceEdgeIndex edge)
  change (∑ edge ∈ selected, (1 : ℚ) / data.sourceEdgeIndex edge) +
      (∑ edge ∈ coarseOldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge) =
        matrix data path profile.first.1.1.1 at hSplit
  rw [hSelected, Finset.sum_filter,
    Finset.sum_pair (source_first_ne_second input profile)] at hSplit
  simp only [hMem ⟨profile.first.1, first_survives input profile⟩ rfl,
    hMem ⟨profile.second.1, second_survives input profile⟩ hSame.symm] at hSplit
  exact hSplit.symm

/-- The old largest-direction column `t₄` consists of its unique selected
occurrence `e₄` and all literal background occurrences. -/
theorem largest_matrix_decomposition (path : StablePath data) :
    matrix data path (largestTarget input profile) =
      (if path = NonDanglingEdge.stablePath
          ⟨profile.largest.1, largest_survives input profile⟩ then
        (1 : ℚ) / data.sourceEdgeIndex profile.largest.1 else 0) +
      ∑ edge ∈ fineOldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  let selected := (occurrences data path (largestTarget input profile)).filter
    (fun edge ↦ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2)
  have hSelected : selected =
      ({profile.largest.1} : Finset data.SourceEdge).filter
        (fun edge ↦ edge ∈ occurrences data path (largestTarget input profile)) := by
    ext edge
    simp only [selected, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hMem, hRel⟩
      exact ⟨selected_largest_eq input profile edge hMem hRel, hMem⟩
    · rintro ⟨rfl, hMem⟩
      exact ⟨hMem, incident_wall_rel input profile.largest⟩
  have hMem (edge : NonDanglingEdge data)
      (hTarget : edge.1.1.1 = largestTarget input profile) :
      edge.1 ∈ occurrences data path (largestTarget input profile) ↔
        path = edge.stablePath := by
    rw [mem_occurrences]
    exact ⟨fun h ↦ h.1.choose_spec.symm, fun h ↦ ⟨⟨edge.2, h.symm⟩, hTarget⟩⟩
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (occurrences data path (largestTarget input profile))
    (fun edge ↦ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2)
    (fun edge ↦ (1 : ℚ) / data.sourceEdgeIndex edge)
  change (∑ edge ∈ selected, (1 : ℚ) / data.sourceEdgeIndex edge) +
      (∑ edge ∈ fineOldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge) =
        matrix data path (largestTarget input profile) at hSplit
  rw [hSelected, Finset.sum_filter, Finset.sum_singleton] at hSplit
  simp only [hMem ⟨profile.largest.1, largest_survives input profile⟩ rfl] at hSplit
  exact hSplit.symm

/-- `k₄ = k₂ + k₃` in `ℚ`: the doubled direction exhausts the block. -/
theorem largest_index_cast (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (data.sourceEdgeIndex profile.largest.1 : ℚ) =
      (data.sourceEdgeIndex profile.first.1 : ℚ) +
        (data.sourceEdgeIndex profile.second.1 : ℚ) := by
  have hDoubled := profile.doubled_direction hSame
  have hNat : data.sourceEdgeIndex profile.largest.1 =
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 := by
    omega
  exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℚ)) hNat

/-- **Equation (4) at column level.**  Figure 30's two new columns add to the
two old columns `t₃` and `t₄` — but *crossed*: `M⁽¹⁾`'s new column carries the
selected coefficient of the old `t₄` column and the background of the old `t₃`
column, and `M⁽²⁾`'s new column carries the two selected coefficients of the
old `t₃` column and the background of the old `t₄` column. -/
theorem new_columns_add_eq_old
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (path : StablePath data) :
    matrix (coarseCandidate input profile hSame).datum
        (coarseStablePathEquiv input profile hSame path)
        (occurrenceEquiv target wall (coarseCandidate input profile hSame).right none) +
      matrix (fineCandidate input profile hSame).datum
        (fineStablePathEquiv input profile hSame path)
        (occurrenceEquiv target wall (fineCandidate input profile hSame).right none) =
      matrix data path profile.first.1.1.1 +
        matrix data path (largestTarget input profile) := by
  classical
  rw [coarse_matrix_new_on_old_row input profile hSame,
    fine_matrix_new_on_old_row input profile hSame,
    doubled_matrix_decomposition input profile hSame,
    largest_matrix_decomposition input profile,
    largest_index_cast input profile hSame]
  ring

/-! ## The two-member family, in one common coordinate system -/

section Family

variable (hSame : profile.first.1.1.1 = profile.second.1.1.1)

/-- The two actual Figure 30 members.  Both live over the **same** incoming
datum `data`, so no branch swap and no gauge family is involved. -/
noncomputable def members : Fin 2 → BalancedGlobal.Candidate target degree data wall :=
  ![coarseCandidate input profile hSame, fineCandidate input profile hSame]

/-- The same two members with their derived global validity. -/
noncomputable def candidates : Fin 2 → BalancedGlobal.CertifiedCandidate data :=
  fun position ↦ (members input profile hSame position).certified

/-- The common source rows are transported by the actual coarse and fine
stable-path equivalences. -/
noncomputable def rowEquiv (position : Fin 2) : StablePath data ≃
    StablePath (members input profile hSame position).datum :=
  Fin.cases (coarseStablePathEquiv input profile hSame)
    (Fin.cases (fineStablePathEquiv input profile hSame) (fun i ↦ Fin.elim0 i)) position

/-- Retained target occurrences use the canonical expansion labelling and
`none` names the new wall edge. -/
noncomputable def columnEquiv (position : Fin 2) : Option target.edges ≃
    (candidates input profile hSame position).outgoingTarget.edges :=
  Fin.cases (occurrenceEquiv target wall (coarseCandidate input profile hSame).right)
    (Fin.cases (occurrenceEquiv target wall (fineCandidate input profile hSame).right)
      (fun i ↦ Fin.elim0 i)) position

/-- Natural matrices in the common old row and target-occurrence coordinates. -/
noncomputable def commonMatrix (position : Fin 2) :
    Matrix (StablePath data) (Option target.edges) ℚ :=
  fun path place ↦ matrix (members input profile hSame position).datum
    (rowEquiv input profile hSame position path)
    (columnEquiv input profile hSame position place)

theorem commonMatrix_retained (position : Fin 2) (path : StablePath data)
    (place : target.edges) :
    commonMatrix input profile hSame position path (some place) =
      matrix data path place := by
  fin_cases position
  · exact coarse_matrix_retained input profile hSame path place
  · exact fine_matrix_retained input profile hSame path place

/-- **Equation (4) at column level, in common coordinates.**  The crossed
identity of `new_columns_add_eq_old`. -/
theorem commonMatrix_new_add (path : StablePath data) :
    commonMatrix input profile hSame 0 path none +
        commonMatrix input profile hSame 1 path none =
      matrix data path profile.first.1.1.1 +
        matrix data path (largestTarget input profile) :=
  new_columns_add_eq_old input profile hSame path

section Square

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling
    (members input profile hSame 0).datum coordinate)

/-- A single honest member labelling supplies only the finite coordinate
order.  The second member is labelled through the geometric equivalences. -/
noncomputable def sourceCoordinates : StablePath data ≃ coordinate :=
  (rowEquiv input profile hSame 0).trans initial.row

noncomputable def targetCoordinates : coordinate ≃ Option target.edges :=
  initial.targetEdge.trans (columnEquiv input profile hSame 0).symm

/-- The induced honest square labelling of both members. -/
noncomputable def labelling (position : Fin 2) :
    StableLengthMatrixLabelling (members input profile hSame position).datum coordinate where
  row := (rowEquiv input profile hSame position).symm.trans
    (sourceCoordinates input profile hSame initial)
  targetEdge := (targetCoordinates input profile hSame initial).trans
    (columnEquiv input profile hSame position)

/-- The honest square length matrix of one member. -/
noncomputable def squareMatrix (position : Fin 2) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (labelling input profile hSame initial position).presentation

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn : coordinate :=
  (targetCoordinates input profile hSame initial).symm none

theorem squareMatrix_common (position : Fin 2) (row column : coordinate) :
    squareMatrix input profile hSame initial position row column =
      commonMatrix input profile hSame position
        ((sourceCoordinates input profile hSame initial).symm row)
        (targetCoordinates input profile hSame initial column) :=
  labelling_matrix_eq (labelling input profile hSame initial position) row column

theorem squareMatrix_retained (position : Fin 2) (row : coordinate)
    (place : target.edges) :
    squareMatrix input profile hSame initial position row
        ((targetCoordinates input profile hSame initial).symm (some place)) =
      matrix data ((sourceCoordinates input profile hSame initial).symm row) place := by
  rw [squareMatrix_common, Equiv.apply_symm_apply, commonMatrix_retained]

theorem squareMatrix_new (position : Fin 2) (row : coordinate) :
    squareMatrix input profile hSame initial position row
        (wallColumn input profile hSame initial) =
      commonMatrix input profile hSame position
        ((sourceCoordinates input profile hSame initial).symm row) none := by
  rw [squareMatrix_common, wallColumn, Equiv.apply_symm_apply]

/-- The two members' matrices agree away from the regrown wall column.  This
is the retained-column theorem and nothing else: no nonsingularity and no
supplied cofactor correspondence enter. -/
theorem matrices_agree (first second : Fin 2) :
    AgreeOffColumn (squareMatrix input profile hSame initial first)
      (squareMatrix input profile hSame initial second)
      (wallColumn input profile hSame initial) := by
  intro row column hColumn
  rw [squareMatrix_common, squareMatrix_common]
  cases hPlace : targetCoordinates input profile hSame initial column with
  | none => exact (hColumn ((Equiv.eq_symm_apply _).mpr hPlace)).elim
  | some place => rw [commonMatrix_retained, commonMatrix_retained]

/-- **The common cofactors.**  The wall row of the adjugate is literally the
same for both members, because their matrices agree off the wall column. -/
theorem common_cofactors (position : Fin 2) (row : coordinate) :
    (squareMatrix input profile hSame initial position).adjugate
        (wallColumn input profile hSame initial) row =
      (squareMatrix input profile hSame initial 0).adjugate
        (wallColumn input profile hSame initial) row :=
  adjugate_wallRow_eq_of_agreeOffColumn
    (matrices_agree input profile hSame initial position 0) row

/-- Each old column's cofactor-weighted contribution vanishes: it is an
off-diagonal entry of `adjugate A * A = det A • 1`. -/
theorem old_column_annihilation (place : target.edges) :
    columnContribution (squareMatrix input profile hSame initial 0)
      (wallColumn input profile hSame initial)
      ((targetCoordinates input profile hSame initial).symm (some place)) = 0 := by
  apply columnContribution_eq_zero
  intro h
  have hLabels := (targetCoordinates input profile hSame initial).symm.injective h
  cases hLabels

/-- **Equation (4)**, for the two actual Figure 30 members in their induced
common labellings.  Neither determinant is assumed nonzero, and the weights
are the unit weights `![1, 1]` that `BalancingRemaining.balance_w3_nd3_t3`
also uses: the two determinants enter the sum with equal coefficients. -/
theorem determinant_balance :
    (squareMatrix input profile hSame initial 0).det +
      (squareMatrix input profile hSame initial 1).det = 0 := by
  classical
  let A := squareMatrix input profile hSame initial
  let k := wallColumn input profile hSame initial
  let doubledColumn :=
    (targetCoordinates input profile hSame initial).symm (some profile.first.1.1.1)
  let largestColumn :=
    (targetCoordinates input profile hSame initial).symm
      (some (largestTarget input profile))
  have hDet (position : Fin 2) : (A position).det =
      ∑ row, A position row k * (A 0).adjugate k row :=
    det_eq_sum_wallColumn_mul_commonCofactor
      (matrices_agree input profile hSame initial position 0)
  have hColumn (row : coordinate) : A 0 row k + A 1 row k =
      A 0 row doubledColumn + A 0 row largestColumn := by
    dsimp only [A, k, doubledColumn, largestColumn]
    rw [squareMatrix_new, squareMatrix_new,
      squareMatrix_retained, squareMatrix_retained]
    exact commonMatrix_new_add input profile hSame _
  calc
    (A 0).det + (A 1).det =
        ∑ row, (A 0 row k + A 1 row k) * (A 0).adjugate k row := by
      rw [hDet 0, hDet 1]
      simp only [add_mul, Finset.sum_add_distrib]
    _ = columnContribution (A 0) k doubledColumn +
        columnContribution (A 0) k largestColumn := by
      simp_rw [hColumn]
      simp only [columnContribution, add_mul, Finset.sum_add_distrib]
    _ = 0 := by
      rw [old_column_annihilation input profile hSame initial,
        old_column_annihilation input profile hSame initial]
      ring

theorem positiveBalance : BalancingValencyTwo.PositiveBalance ![1, 1]
    (fun position ↦ (squareMatrix input profile hSame initial position).det) := by
  constructor
  · intro position
    fin_cases position <;> norm_num
  · have h := determinant_balance input profile hSame initial
    simpa [Fin.sum_univ_succ] using h

/-! ## The balanced family -/

/-- The two actual Figure 30 members with their honest stable-length matrices
and the proved Equation (4) balance.  A possibly singular member is kept. -/
noncomputable def family : BalancedGlobal.Family (coordinate := coordinate) 2 data where
  candidate := candidates input profile hSame
  matrix := squareMatrix input profile hSame initial
  wallColumn := wallColumn input profile hSame initial
  weight := ![1, 1]
  positiveBalance := positiveBalance input profile hSame initial
  agreeOffWall := matrices_agree input profile hSame initial

theorem family_matrix_is_honest (position : Fin 2) :
    (family input profile hSame initial).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix
        (labelling input profile hSame initial position).presentation := rfl

/-- The same family before forgetting the actual candidates and their honest
presentations: the form a semantic positive exit consumes.  Both members are
`BalancedGlobal.Candidate`s on the one datum `data`. -/
noncomputable def honestPresentedFamily :
    BalancedGlobal.PresentedFamily (coordinate := coordinate) 2 data wall where
  candidate := members input profile hSame
  presentation := fun position ↦ (labelling input profile hSame initial position).presentation
  wallColumn := wallColumn input profile hSame initial
  weight := ![1, 1]
  positiveBalance := positiveBalance input profile hSame initial
  agreeOffWall := matrices_agree input profile hSame initial

theorem honestPresentedFamily_toFamily :
    (honestPresentedFamily input profile hSame initial).toFamily =
      family input profile hSame initial := rfl

/-- Any nonsingular chosen member has an actual valid opposite-sign member;
no nonsingularity hypothesis is imposed on the other one. -/
theorem exists_valid_opposite (incoming : Fin 2)
    (hIncoming : (squareMatrix input profile hSame initial incoming).det ≠ 0) :
    ∃ outgoing, (members input profile hSame outgoing).datum.Valid ∧
      (squareMatrix input profile hSame initial incoming).det *
        (squareMatrix input profile hSame initial outgoing).det < 0 :=
  (family input profile hSame initial).exists_valid_opposite input.valid incoming hIncoming

/-- **The identified-member positive exit.**  For an identified incoming
member of the actual Figure 30 pair whose honest square matrix is nonsingular,
Equation (4) selects a valid opposite-sign member and the one-column cone-wall
calculation supplies the positive rational step together with its cleared
rank-one pencil.  Only the chosen incoming member is assumed nonsingular. -/
theorem exists_valid_positive_exit_with_pencil
    (hTargetConnected : graph_connected target) (hTargetGenus : genus target = 0)
    (root : target.V) (incoming : Fin 2)
    (hIncoming : (squareMatrix input profile hSame initial incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 2 → coordinate → ℚ)
    (hz : z (wallColumn input profile hSame initial) = 0)
    (hzpos : ∀ i, i ≠ wallColumn input profile hSame initial → 0 < z i)
    (hSystems : ∀ outgoing,
      (squareMatrix input profile hSame initial outgoing).det ≠ 0 →
      (squareMatrix input profile hSame initial incoming).mulVec incomingVelocity =
        (squareMatrix input profile hSame initial outgoing).mulVec
          (outgoingVelocity outgoing))
    (hIncomingDirection :
      incomingVelocity (wallColumn input profile hSame initial) < 0) :
    ∃ outgoing,
      (members input profile hSame outgoing).datum.Valid ∧
      (squareMatrix input profile hSame initial incoming).det *
        (squareMatrix input profile hSame initial outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (squareMatrix input profile hSame initial outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (squareMatrix input profile hSame initial incoming).mulVec z +
            t • (squareMatrix input profile hSame initial incoming).mulVec
              incomingVelocity ∧
        Nonempty (BalancedGlobal.Candidate.ClearedPencil
          (members input profile hSame outgoing)
          (labelling input profile hSame initial outgoing).presentation
          (z + t • outgoingVelocity outgoing)) :=
  (honestPresentedFamily input profile hSame initial).exists_valid_positive_exit_with_pencil
    input.valid hTargetConnected hTargetGenus root incoming hIncoming z incomingVelocity
    outgoingVelocity hz hzpos hSystems hIncomingDirection

end Square

/-! ## Canonical square coordinates -/

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- The existing W3 source census supplies a canonical square coordinate
order; it does not assert any extra geometric row matching. -/
noncomputable def canonicalRowOrder : StablePath data ≃ Option target.edges :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_option, Multiset.card_coe]
    exact input.stablePath_card)

noncomputable def canonicalInitialLabelling : StableLengthMatrixLabelling
    (members input profile hSame 0).datum (Option target.edges) where
  row := (rowEquiv input profile hSame 0).symm.trans (canonicalRowOrder input)
  targetEdge := columnEquiv input profile hSame 0

noncomputable def canonicalMatrix (position : Fin 2) :
    Matrix (Option target.edges) (Option target.edges) ℚ :=
  squareMatrix input profile hSame (canonicalInitialLabelling input profile hSame) position

/-- **Equation (4) with no supplied square labelling.** -/
theorem canonical_determinant_balance :
    (canonicalMatrix input profile hSame 0).det +
      (canonicalMatrix input profile hSame 1).det = 0 :=
  determinant_balance input profile hSame (canonicalInitialLabelling input profile hSame)

noncomputable def canonicalFamily :
    BalancedGlobal.Family (coordinate := Option target.edges) 2 data :=
  family input profile hSame (canonicalInitialLabelling input profile hSame)

theorem canonicalFamily_matrix_is_honest (position : Fin 2) :
    (canonicalFamily input profile hSame).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix
        (labelling input profile hSame
          (canonicalInitialLabelling input profile hSame) position).presentation := rfl

/-- The canonical family in presented form, retaining the two actual Figure 30
members. -/
noncomputable def canonicalPresentedFamily :
    BalancedGlobal.PresentedFamily (coordinate := Option target.edges) 2 data wall :=
  honestPresentedFamily input profile hSame (canonicalInitialLabelling input profile hSame)

theorem canonicalPresentedFamily_candidate (position : Fin 2) :
    (canonicalPresentedFamily input profile hSame).candidate position =
      members input profile hSame position := rfl

end Family

end DraismaVargas.LocalCases.W3Nd3CommonBalance
