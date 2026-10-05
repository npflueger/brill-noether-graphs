module

public import DraismaVargas.Infrastructure.LengthMatrix
public import Utilities.Foundations.TreeFamily
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# Nonsingularity of a seed length matrix

A march of the Draisma--Vargas construction starts from a seed whose length
matrix is nonsingular, and no march can start without it.  The nonsingularity
has to hold uniformly in the size of the seed, which neither a fixed numeric
evaluation (a determinant computed by `decide` at one genus) nor a cofactor
*balance* identity (`BalancingValencyTwo`) provides.  Nothing here evaluates a
concrete structure; every statement is uniform in the size parameters.

Recall the entry formula (`Infrastructure.LengthMatrix`): the `(h, t)`
entry is `∑_{e ∈ path h, φ(e) = t} 1 / m(e)`.  So the matrix is determined by
the *index pattern* of a presentation -- which target occurrence each displayed
source block lies over, and with what dilation index.

## 1.  Positivity, and what it buys

Every coefficient `1 / m(e)` is positive and every other contribution is zero,
so a length-matrix entry is a sum of positive terms with no cancellation
available: `matrix_pos_of_mem` and `matrix_eq_zero_of_forall_ne` say that an
entry is **strictly positive exactly when** the row displays at least one block
over that column, and zero otherwise.  This is the reason a purely combinatorial
index pattern can decide nonsingularity: the numerical values never conspire.

## 2.  Two index patterns

* `DiagonalPattern` -- every displayed block of a row lies over that row's own
  column, and no row is empty.  Then the matrix is diagonal with positive
  diagonal (`DiagonalPattern.matrix_eq_diagonal`) and `det > 0`.
* `TriangularPattern` -- for some linear order on the coordinates, every
  displayed block lies over a column `≤` the row, and some block lies over the
  row's own column.  Then the matrix is lower triangular with positive diagonal
  and `det > 0` (`TriangularPattern.det_pos`).

Both are statements about honest `LengthMatrixPresentation`s of honest
`GluingDatum`s; nothing is assumed about the datum.

## 3.  A realisation, and what it does and does not cover

`discreteEdgeDatum` is the degree-two cover of an arbitrary target that is
discrete over every edge occurrence; the vertex partition is a free parameter,
because the discrete partition refines everything, so both refinement receipts
are automatic.  `fibrePresentation` displays, over each target occurrence, its
whole fibre -- the two index-one blocks.  `fibrePresentation_matrix` computes the
length matrix to be `2 · I`, and `fibrePresentation_det_ne_zero` is its
nonsingularity, uniformly in the target and in the coordinate indexing.
`starDatum` instantiates this over `TreeFamily.starGraph n`, whose occurrence
type is matched with `Fin n` by `starIndex`.

The source graph of `starDatum n` is the `n`-banana subdivided at the leaves:
two source vertices over the centre, one over each leaf, two source edges over
each ray.  `card_sourceEdge_starDatum`, `card_sourceVertex_starDatum` and
`genus_sourceGraph_starDatum` prove `2n` edges on `n + 2` vertices and genus
`n - 1`, so the genus really does grow with the parameter.

What this does **not** claim. The *stable model* of that source is the
`n`-banana, whose stable edges are exactly the displayed fibres -- which is why
`fibrePresentation` is the honest Draisma--Vargas presentation here and not an
arbitrary choice of paths. **That identification is a hand computation and is
not formalised in this file.** Moreover the `n`-banana is trivalent only for
`n = 3`, where it is the theta graph of genus two; so this family is a
full-dimensional seed for a *trivalent* stable type only in genus two, and for
larger `n` it is a valid degree-two cover with a nonsingular square length
matrix but not a `3g - 3`-dimensional seed. It is recorded here because it is
the base case of the Draisma--Vargas recursion and because it shows the diagonal
criterion is not vacuous.

## 4.  The index pattern a tripod step produces, and the determinant recursion

The Cools--Draisma recursion (the tripod step, which Draisma--Vargas Part I
uses for its initial families) goes from genus `g` to genus `g + 2` and
degree `d` to `d + 1`: three target edges are subdivided, a pendant *arm* is
attached at each subdivision point, a new sheet `d + 1` is carried over the whole
old tree, each arm is discrete over its interior, and at each arm's leaf the new
sheet is glued to one chosen old sheet.  Counting: `3` new columns from the
subdivisions and `3` arm columns, against `3` new rows from the split stable
edges and `3` tripod legs, i.e. `3g - 3 + 6 = 3(g + 2) - 3` on both sides.

Working out what each new row displays gives the pattern, and it is *not*
diagonal:

* an **arm column** is met by exactly one row, the corresponding leg, and there
  with coefficient `2` -- the leg runs out along the arm and back, over two
  index-one blocks.  No other stable edge crosses an arm: the other `d - 1`
  blocks over an arm are dangling and are pruned;
* a **leg row** additionally runs through the new sheet's copy of the old tree,
  so it meets old columns as well; the arm block is therefore the only place the
  new columns are seen;
* an **unsplit old row** sees both halves of a subdivided column exactly as it
  saw the whole column, because each of its blocks over the old occurrence
  becomes a block over each half;
* the **two halves of a split old row** add up to the old row on every column,
  and they differ on the two halves of the cut column precisely by the
  reciprocal index of the block in whose interior the attachment point was
  chosen.

`det_extend` and `det_subdivision` are those two steps, as determinant
identities.  `det_extend` is the arm step: a fresh column seen by no old row,
with corner `c`, multiplies the determinant by `c`.  `det_subdivision` is the
subdivision step: the hypotheses are the four bullets above, and the conclusion
is that the determinant is multiplied by the *defect*
`δ = A(h₂, e') - A(h₂, e'')`, which is `± 1 / m(β)`.  A full tripod step is three
subdivisions followed by three arms, so on the nose

`det(new) = (∏ᵢ cᵢ) · (∏ᵢ δᵢ) · det(old)`, with `cᵢ = 2` and `δᵢ = ± 1 / m(βᵢ)`.

Both steps are stated for an arbitrary finite index type, so the three-fold
iteration is just the same lemma applied to `index ⊕ Unit` again; nothing is
fixed-size.

**What is not done here.**  These two lemmas are about matrices, not about
covers: they say *given* that the extended matrix stands to the old one in the
displayed relation, the determinant behaves so.  Producing a tripod-extended
`GluingDatum` together with a `LengthMatrixPresentation` whose matrix satisfies
those hypotheses is **not** done in this file, so §4 is a template: honest as a
matrix identity, and exactly the identity the geometry calls for, without the
realisation.  The construction of the main theorem starts instead from the
caterpillar seed of Vargas, Part II (`CaterpillarRows`), whose matrix is
diagonal.

**Is a triangular pattern available?**  Diagonal is: §3 realises it, and the
genus-two theta seed is the case `n = 3` there.  Triangular survives one tripod
step in the worked genus-four example (order the rows `h₁ᵢ, h₂ᵢ, legᵢ` and the
columns `eᵢ', eᵢ'', armᵢ`; the matrix becomes lower triangular with diagonal
`1, 2, 2` per block, determinant `64`), but that computation depends on choosing
each attachment point at the *first* crossing of the cut column by its stable
edge, so that `h₁` meets only the near half.  For an arbitrary choice `h₁` meets
both halves and triangularity fails while the determinant formula of §4 still
holds.  So the triangular criterion is real and usable, but the invariant
that actually propagates through the recursion is the determinant identity,
not triangularity.
-/
namespace DraismaVargas.LocalCases.SeedDeterminant

open Matrix
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [DecidableEq coordinate]

/-! ## 1.  Every length-matrix entry is a sum of positive terms -/

section Positivity

variable (presentation : data.LengthMatrixPresentation coordinate)

/-- A matrix coefficient is never negative: it is either `0` or `1 / m(e)`. -/
theorem coefficient_nonneg (edge : data.SourceEdge) (column : coordinate) :
    0 ≤ LengthMatrixPresentation.coefficient presentation edge column := by
  have hIndex : (0 : ℚ) ≤ (data.sourceEdgeIndex edge : ℚ) := by positivity
  simp only [LengthMatrixPresentation.coefficient]
  split
  · exact div_nonneg zero_le_one hIndex
  · exact le_rfl

/-- On the target column carrying a source edge, the coefficient is strictly
positive: `1 / m(e)` with `m(e) ≥ 1`. -/
theorem coefficient_pos (edge : data.SourceEdge) (column : coordinate)
    (hTarget : presentation.targetEdge column = edge.1.1) :
    0 < LengthMatrixPresentation.coefficient presentation edge column := by
  have hColumn : column = presentation.targetEdge.symm edge.1.1 := by
    apply presentation.targetEdge.injective
    simpa using hTarget
  have hIndex : (0 : ℚ) < (data.sourceEdgeIndex edge : ℚ) := by
    exact_mod_cast data.sourceEdgeIndex_pos edge
  simp only [LengthMatrixPresentation.coefficient, ite_eq_left hColumn]
  exact div_pos one_pos hIndex

theorem row_nil (presentation : data.LengthMatrixPresentation coordinate)
    (column : coordinate) :
    LengthMatrixPresentation.row presentation [] column = 0 := rfl

theorem row_cons (presentation : data.LengthMatrixPresentation coordinate)
    (edge : data.SourceEdge) (rest : List data.SourceEdge)
    (column : coordinate) :
    LengthMatrixPresentation.row presentation (edge :: rest) column =
      LengthMatrixPresentation.coefficient presentation edge column +
        LengthMatrixPresentation.row presentation rest column := rfl

/-- Every entry of every path row is nonnegative. -/
theorem row_nonneg (path : List data.SourceEdge) (column : coordinate) :
    0 ≤ LengthMatrixPresentation.row presentation path column := by
  refine List.sum_nonneg ?_
  intro value hvalue
  obtain ⟨edge, -, rfl⟩ := List.mem_map.mp hvalue
  exact coefficient_nonneg presentation edge column

/-- A path row is strictly positive on any column carrying one of its source
edges. -/
theorem row_pos_of_mem (path : List data.SourceEdge) (column : coordinate)
    (edge : data.SourceEdge) (hEdge : edge ∈ path)
    (hTarget : presentation.targetEdge column = edge.1.1) :
    0 < LengthMatrixPresentation.row presentation path column := by
  refine lt_of_lt_of_le (coefficient_pos presentation edge column hTarget) ?_
  refine List.single_le_sum ?_ _ (List.mem_map_of_mem hEdge)
  intro value hvalue
  obtain ⟨other, -, rfl⟩ := List.mem_map.mp hvalue
  exact coefficient_nonneg presentation other column

/-- A path row vanishes on any column carrying none of its source edges. -/
theorem row_eq_zero_of_forall_ne (path : List data.SourceEdge)
    (column : coordinate)
    (hTarget : ∀ edge ∈ path, presentation.targetEdge column ≠ edge.1.1) :
    LengthMatrixPresentation.row presentation path column = 0 := by
  induction path with
  | nil => simp [LengthMatrixPresentation.row]
  | cons edge rest ih =>
      have hHead := hTarget edge (List.mem_cons_self)
      have hRest : ∀ other ∈ rest,
          presentation.targetEdge column ≠ other.1.1 := fun other hother =>
        hTarget other (List.mem_cons_of_mem _ hother)
      simp only [LengthMatrixPresentation.row, List.map_cons, List.sum_cons]
      rw [LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
        presentation edge column hHead, zero_add]
      exact ih hRest

/-- A matrix entry is strictly positive on any column carrying one of the
row's source edges. -/
theorem matrix_pos_of_mem (sourceRow column : coordinate)
    (edge : data.SourceEdge) (hEdge : edge ∈ presentation.path sourceRow)
    (hTarget : presentation.targetEdge column = edge.1.1) :
    0 < LengthMatrixPresentation.matrix presentation sourceRow column :=
  row_pos_of_mem presentation _ column edge hEdge hTarget

/-- A matrix entry vanishes on any column carrying none of the row's source
edges. -/
theorem matrix_eq_zero_of_forall_ne (sourceRow column : coordinate)
    (hTarget : ∀ edge ∈ presentation.path sourceRow,
      presentation.targetEdge column ≠ edge.1.1) :
    LengthMatrixPresentation.matrix presentation sourceRow column = 0 :=
  row_eq_zero_of_forall_ne presentation _ column hTarget

end Positivity

/-! ## 2.  Two index patterns that force nonsingularity -/

section Patterns

/-- **The diagonal index pattern.**  Every source block displayed by a row lies
over that row's own target column, and no row is empty. -/
structure DiagonalPattern (presentation : data.LengthMatrixPresentation coordinate) :
    Prop where
  /-- Each displayed source block lies over the row's own target occurrence. -/
  liesOver : ∀ sourceRow, ∀ edge ∈ presentation.path sourceRow,
    edge.1.1 = presentation.targetEdge sourceRow
  /-- No displayed stable path is empty. -/
  pathNeNil : ∀ sourceRow, presentation.path sourceRow ≠ []

namespace DiagonalPattern

variable {presentation : data.LengthMatrixPresentation coordinate}

theorem matrix_apply_eq_zero (pattern : DiagonalPattern presentation)
    {sourceRow column : coordinate} (hne : column ≠ sourceRow) :
    LengthMatrixPresentation.matrix presentation sourceRow column = 0 := by
  refine matrix_eq_zero_of_forall_ne presentation sourceRow column ?_
  intro edge hEdge hTarget
  exact hne (presentation.targetEdge.injective
    (hTarget.trans (pattern.liesOver sourceRow edge hEdge)))

theorem matrix_diag_pos (pattern : DiagonalPattern presentation)
    (sourceRow : coordinate) :
    0 < LengthMatrixPresentation.matrix presentation sourceRow sourceRow := by
  obtain ⟨edge, hEdge⟩ := List.exists_mem_of_ne_nil _ (pattern.pathNeNil sourceRow)
  exact matrix_pos_of_mem presentation sourceRow sourceRow edge hEdge
    (pattern.liesOver sourceRow edge hEdge).symm

theorem matrix_eq_diagonal (pattern : DiagonalPattern presentation) :
    LengthMatrixPresentation.matrix presentation =
      Matrix.diagonal fun sourceRow ↦
        LengthMatrixPresentation.matrix presentation sourceRow sourceRow := by
  funext sourceRow column
  by_cases hrc : column = sourceRow
  · subst hrc
    rw [Matrix.diagonal_apply_eq]
  · rw [pattern.matrix_apply_eq_zero hrc,
      Matrix.diagonal_apply_ne _ (Ne.symm hrc)]

variable [Fintype coordinate]

/-- A diagonal index pattern has strictly positive determinant. -/
theorem det_pos (pattern : DiagonalPattern presentation) :
    0 < (LengthMatrixPresentation.matrix presentation).det := by
  rw [pattern.matrix_eq_diagonal, Matrix.det_diagonal]
  exact Finset.prod_pos fun sourceRow _ ↦ pattern.matrix_diag_pos sourceRow

/-- **Nonsingularity from the diagonal pattern.** -/
theorem det_ne_zero (pattern : DiagonalPattern presentation) :
    (LengthMatrixPresentation.matrix presentation).det ≠ 0 :=
  pattern.det_pos.ne'

end DiagonalPattern

/-- **The triangular index pattern.**  Every source block displayed by a row
lies over a target column at most the row's own, and at least one lies over the
row's own column.  Positivity of the coefficients does the rest: no
cancellation can occur on the diagonal. -/
structure TriangularPattern [LinearOrder coordinate]
    (presentation : data.LengthMatrixPresentation coordinate) : Prop where
  /-- No displayed source block lies over a later target column. -/
  le : ∀ sourceRow, ∀ edge ∈ presentation.path sourceRow,
    presentation.targetEdge.symm edge.1.1 ≤ sourceRow
  /-- Some displayed source block lies over the row's own target column. -/
  meets : ∀ sourceRow, ∃ edge ∈ presentation.path sourceRow,
    presentation.targetEdge.symm edge.1.1 = sourceRow

namespace TriangularPattern

variable [LinearOrder coordinate]
  {presentation : data.LengthMatrixPresentation coordinate}

theorem isLowerTriangular (pattern : TriangularPattern presentation) :
    (LengthMatrixPresentation.matrix presentation).IsLowerTriangular := by
  intro sourceRow column hlt
  have hStrict : sourceRow < column := hlt
  refine matrix_eq_zero_of_forall_ne presentation sourceRow column ?_
  intro edge hEdge hTarget
  have hColumn : presentation.targetEdge.symm edge.1.1 = column := by
    rw [← hTarget, Equiv.symm_apply_apply]
  exact absurd (hColumn ▸ pattern.le sourceRow edge hEdge) (not_le.mpr hStrict)

theorem matrix_diag_pos (pattern : TriangularPattern presentation)
    (sourceRow : coordinate) :
    0 < LengthMatrixPresentation.matrix presentation sourceRow sourceRow := by
  obtain ⟨edge, hEdge, hColumn⟩ := pattern.meets sourceRow
  refine matrix_pos_of_mem presentation sourceRow sourceRow edge hEdge ?_
  rw [← hColumn, Equiv.apply_symm_apply]

variable [Fintype coordinate]

/-- A triangular index pattern has strictly positive determinant, namely the
product of the diagonal stable-path sums. -/
theorem det_pos (pattern : TriangularPattern presentation) :
    0 < (LengthMatrixPresentation.matrix presentation).det := by
  rw [Matrix.det_of_isLowerTriangular _ pattern.isLowerTriangular]
  exact Finset.prod_pos fun sourceRow _ ↦ pattern.matrix_diag_pos sourceRow

/-- **Nonsingularity from the triangular pattern.** -/
theorem det_ne_zero (pattern : TriangularPattern presentation) :
    (LengthMatrixPresentation.matrix presentation).det ≠ 0 :=
  pattern.det_pos.ne'

end TriangularPattern

end Patterns

/-! ## 3.  A realisation over the tree family -/

section StarCover

open DraismaVargas.Infrastructure.TreeFamily

/-- Every block of the discrete partition is a singleton. -/
theorem blockCard_discrete (d : ℕ) (sheet : Fin d) :
    (SheetPartition.discrete d).blockCard sheet = 1 := by
  have hblock : (SheetPartition.discrete d).block sheet = {sheet} := by
    ext other
    simp [SheetPartition.mem_block_iff, SheetPartition.discrete, eq_comm]
  rw [SheetPartition.blockCard, hblock, Finset.card_singleton]

/-- A degree-two cover that is discrete over every target edge occurrence.  The
vertex partition is a free parameter: the two refinement receipts are automatic,
because the discrete partition refines everything. -/
def discreteEdgeDatum (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2) : GluingDatum target 2 where
  degree_pos := by norm_num
  vertexPartition := vertexPartition
  edgePartition := fun _ ↦ SheetPartition.discrete 2
  refines_left := fun _ ↦ SheetPartition.discrete_refines _
  refines_right := fun _ ↦ SheetPartition.discrete_refines _

@[simp] theorem discreteEdgeDatum_edgePartition (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2) (edge : target.edges) :
    (discreteEdgeDatum target vertexPartition).edgePartition edge =
      SheetPartition.discrete 2 := rfl

/-- Every source-edge block of a discrete-edge cover has dilation index one. -/
theorem sourceEdgeIndex_discreteEdgeDatum (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2)
    (edge : (discreteEdgeDatum target vertexPartition).SourceEdge) :
    (discreteEdgeDatum target vertexPartition).sourceEdgeIndex edge = 1 := by
  simpa [GluingDatum.sourceEdgeIndex] using blockCard_discrete 2 edge.1.2

/-- Over a discrete edge partition every sheet is its own block, so every pair
`(occurrence, sheet)` is a source-edge block. -/
theorem discreteEdgeDatum_repr (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2)
    (item : target.edges × Fin 2) :
    ((discreteEdgeDatum target vertexPartition).edgePartition item.1).repr item.2 =
      item.2 := rfl

/-- One source block of a discrete-edge cover, named so that the fibre list is
typed by `SourceEdge` on the nose. -/
def fibreBlock (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2) (edge : target.edges)
    (sheet : Fin 2) : (discreteEdgeDatum target vertexPartition).SourceEdge :=
  ⟨(edge, sheet), discreteEdgeDatum_repr target vertexPartition (edge, sheet)⟩

@[simp] theorem fibreBlock_occurrence (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2) (edge : target.edges)
    (sheet : Fin 2) :
    (fibreBlock target vertexPartition edge sheet).1.1 = edge := rfl

/-- The two source blocks lying over one target occurrence of a discrete-edge
degree-two cover. -/
def fibre (target : CFGraph) (vertexPartition : target.V → SheetPartition 2)
    (edge : target.edges) :
    List (discreteEdgeDatum target vertexPartition).SourceEdge :=
  [fibreBlock target vertexPartition edge 0,
    fibreBlock target vertexPartition edge 1]

variable {coordinate : Type*}

/-- The fibre presentation of a discrete-edge degree-two cover: the displayed
path over a target occurrence is its whole fibre. -/
def fibrePresentation (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2)
    (index : coordinate ≃ target.edges) :
    (discreteEdgeDatum target vertexPartition).LengthMatrixPresentation
      coordinate where
  targetEdge := index
  path := fun column ↦ fibre target vertexPartition (index column)

theorem fibrePresentation_diagonalPattern (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2)
    (index : coordinate ≃ target.edges) :
    DiagonalPattern (fibrePresentation target vertexPartition index) where
  liesOver := by
    intro sourceRow edge hEdge
    simp only [fibrePresentation, fibre] at hEdge
    rcases List.mem_cons.mp hEdge with rfl | hTail
    · rfl
    · rcases List.mem_cons.mp hTail with rfl | hNil
      · rfl
      · simp at hNil
  pathNeNil := by
    intro sourceRow
    simp [fibrePresentation, fibre]

variable [DecidableEq coordinate]

/-- Every coefficient a fibre presentation displays on its own column is `1`:
the blocks have index one. -/
theorem coefficient_fibre (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2)
    (index : coordinate ≃ target.edges) (sourceRow : coordinate)
    (edge : (discreteEdgeDatum target vertexPartition).SourceEdge)
    (hEdge : edge.1.1 = index sourceRow) :
    LengthMatrixPresentation.coefficient
        (fibrePresentation target vertexPartition index) edge sourceRow = 1 := by
  have hIndex := sourceEdgeIndex_discreteEdgeDatum target vertexPartition edge
  have hColumn : sourceRow =
      (fibrePresentation target vertexPartition index).targetEdge.symm edge.1.1 := by
    show sourceRow = index.symm edge.1.1
    rw [hEdge, Equiv.symm_apply_apply]
  simp only [LengthMatrixPresentation.coefficient, ite_eq_left hColumn, hIndex]
  norm_num

/-- Each diagonal entry is `2`: two index-one blocks over the row's own target
occurrence. -/
theorem fibrePresentation_diag (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2)
    (index : coordinate ≃ target.edges) (sourceRow : coordinate) :
    LengthMatrixPresentation.matrix
      (fibrePresentation target vertexPartition index) sourceRow sourceRow =
      2 := by
  have hpath : (fibrePresentation target vertexPartition index).path sourceRow =
      fibre target vertexPartition (index sourceRow) := rfl
  rw [LengthMatrixPresentation.matrix, hpath, fibre, row_cons, row_cons, row_nil,
    coefficient_fibre target vertexPartition index sourceRow _
      (fibreBlock_occurrence _ _ _ _),
    coefficient_fibre target vertexPartition index sourceRow _
      (fibreBlock_occurrence _ _ _ _)]
  norm_num

/-- The fibre presentation of a discrete-edge degree-two cover has length matrix
`2 · I`. -/
theorem fibrePresentation_matrix (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2)
    (index : coordinate ≃ target.edges) :
    LengthMatrixPresentation.matrix
        (fibrePresentation target vertexPartition index) =
      Matrix.diagonal fun _ ↦ (2 : ℚ) := by
  rw [(fibrePresentation_diagonalPattern target vertexPartition
    index).matrix_eq_diagonal]
  congr 1
  funext sourceRow
  exact fibrePresentation_diag target vertexPartition index sourceRow

variable [Fintype coordinate]

/-- **Nonsingularity of the fibre presentation**, uniformly in the target and in
the coordinate indexing. -/
theorem fibrePresentation_det_ne_zero (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2)
    (index : coordinate ≃ target.edges) :
    (LengthMatrixPresentation.matrix
      (fibrePresentation target vertexPartition index)).det ≠ 0 :=
  (fibrePresentation_diagonalPattern target vertexPartition index).det_ne_zero

/-- The degree-two cover of the star with `n` rays whose source is the
`n`-banana: the two sheets stay apart over the centre and are glued at every
leaf. -/
def starDatum (n : ℕ) : GluingDatum (starGraph n) 2 :=
  discreteEdgeDatum (starGraph n) fun vertex : Fin (n + 1) ↦
    if vertex = 0 then SheetPartition.discrete 2 else SheetPartition.indiscrete 2

/-- The star with `n` rays has exactly `n` target occurrences. -/
theorem card_edges_starGraph_type (n : ℕ) :
    Fintype.card (starGraph n).edges = n := by
  rw [Multiset.card_coe, card_edges_starGraph]

/-- So the coordinate type of an `n`-dimensional march can be matched with the
occurrences of the star. -/
noncomputable def starIndex (n : ℕ) : Fin n ≃ (starGraph n).edges :=
  (Fintype.equivFinOfCardEq (card_edges_starGraph_type n)).symm

/-! ### The source graph of the star cover

The two counts below make the phrase "uniformly in the genus" literal: the
source of `starDatum n` has `2n` edges on `n + 2` vertices, so its genus is
`n - 1` and grows with the number of rays.  (Its *stable model* is the
`n`-banana; that identification is the hand computation recorded in the module
docstring and is not formalised.) -/

/-- A discrete-edge cover has exactly two source blocks over every target
occurrence. -/
theorem card_sourceEdge_discreteEdgeDatum (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2) :
    Fintype.card (discreteEdgeDatum target vertexPartition).SourceEdge =
      2 * Fintype.card target.edges := by
  refine Eq.trans (Fintype.card_congr
    (Equiv.subtypeUnivEquiv (discreteEdgeDatum_repr target vertexPartition))) ?_
  rw [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

theorem card_sourceEdge_starDatum (n : ℕ) :
    Fintype.card (starDatum n).SourceEdge = 2 * n := by
  refine Eq.trans (card_sourceEdge_discreteEdgeDatum (starGraph n) _) ?_
  rw [card_edges_starGraph_type]

theorem starDatum_vertexPartition_zero (n : ℕ) :
    (starDatum n).vertexPartition (0 : Fin (n + 1)) =
      SheetPartition.discrete 2 := by
  simp [starDatum, discreteEdgeDatum]

theorem starDatum_vertexPartition_ne_zero (n : ℕ) {vertex : Fin (n + 1)}
    (hvertex : vertex ≠ 0) :
    (starDatum n).vertexPartition vertex = SheetPartition.indiscrete 2 := by
  simp [starDatum, discreteEdgeDatum, hvertex]

/-- Two source vertices over the centre, one over each leaf. -/
theorem card_sourceVertex_starDatum (n : ℕ) :
    Fintype.card (starDatum n).SourceVertex = n + 2 := by
  classical
  have hfibre : ∀ vertex : (starGraph n).V,
      Fintype.card {sheet : Fin 2 //
        ((starDatum n).vertexPartition vertex).repr sheet = sheet} =
        (if vertex = (0 : Fin (n + 1)) then 1 else 0) + 1 := by
    intro vertex
    by_cases hzero : vertex = (0 : Fin (n + 1))
    · subst hzero
      have hall : ∀ sheet : Fin 2,
          ((starDatum n).vertexPartition (0 : Fin (n + 1))).repr sheet = sheet := by
        intro sheet
        rw [starDatum_vertexPartition_zero]
        rfl
      rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hall), Fintype.card_fin]
      split_ifs with hcond
      · rfl
      · exact absurd rfl hcond
    · have hiff : ∀ sheet : Fin 2,
          ((starDatum n).vertexPartition vertex).repr sheet = sheet ↔
            (0 : Fin 2) = sheet := by
        intro sheet
        rw [starDatum_vertexPartition_ne_zero n hzero]
        exact Iff.rfl
      rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff),
        Fintype.card_subtype_eq', ite_eq_right hzero]
  have hzero : (∑ vertex : (starGraph n).V,
      if vertex = (0 : Fin (n + 1)) then 1 else 0) = 1 := by
    refine Eq.trans (Finset.sum_eq_single (0 : Fin (n + 1)) ?_ ?_) ?_
    · intro other _ hother
      exact ite_eq_right hother
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
    · split_ifs with hcond
      · rfl
      · exact absurd rfl hcond
  refine Eq.trans (Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    fun vertex (sheet : Fin 2) ↦
      ((starDatum n).vertexPartition vertex).repr sheet = sheet)) ?_
  rw [Fintype.card_sigma]
  simp only [hfibre]
  rw [Finset.sum_add_distrib, hzero, Finset.sum_const, Finset.card_univ,
    card_vertices_starGraph, smul_eq_mul, mul_one]
  omega

/-- **The source of the star cover has genus `n - 1`.** -/
theorem genus_sourceGraph_starDatum (n : ℕ) :
    genus (starDatum n).sourceGraph = (n : ℤ) - 1 := by
  have hedges : Multiset.card (starDatum n).sourceGraph.edges =
      Fintype.card (starDatum n).SourceEdge := by
    show Multiset.card
      (((Finset.univ : Finset (starDatum n).SourceEdge).val.map
        (starDatum n).sourceEnds)) = _
    rw [Multiset.card_map, ← Finset.card_def, Finset.card_univ]
  have hvertices : Fintype.card (starDatum n).sourceGraph.V =
      Fintype.card (starDatum n).SourceVertex :=
    Fintype.card_congr (Equiv.refl _)
  rw [genus, hedges, hvertices, card_sourceEdge_starDatum,
    card_sourceVertex_starDatum]
  push_cast
  ring

/-- **The seed matrix of the degree-two star cover is nonsingular, uniformly in
the number of rays.** -/
theorem starDatum_det_ne_zero (n : ℕ) (index : Fin n ≃ (starGraph n).edges) :
    (LengthMatrixPresentation.matrix
      (fibrePresentation (starGraph n)
        (fun vertex : Fin (n + 1) ↦
          if vertex = 0 then SheetPartition.discrete 2
            else SheetPartition.indiscrete 2) index)).det ≠ 0 :=
  fibrePresentation_det_ne_zero _ _ index

end StarCover

/-! ## 4.  The two determinant steps of a tripod extension -/

section TripodSteps

variable {index : Type*} [Fintype index] [DecidableEq index]

/-- **The pendant step.**  A new column met by no old row, and met by the new
row with a nonzero coefficient, multiplies the determinant by that
coefficient. -/
theorem det_extend (old : Matrix index index ℚ)
    (extended : Matrix (index ⊕ Unit) (index ⊕ Unit) ℚ) (corner : ℚ)
    (hOld : ∀ sourceRow column,
      extended (Sum.inl sourceRow) (Sum.inl column) = old sourceRow column)
    (hZero : ∀ sourceRow fresh,
      extended (Sum.inl sourceRow) (Sum.inr fresh) = 0)
    (hCorner : ∀ freshRow freshColumn,
      extended (Sum.inr freshRow) (Sum.inr freshColumn) = corner) :
    extended.det = old.det * corner := by
  have hBlocks : extended = Matrix.fromBlocks old 0
      (Matrix.of fun fresh column ↦ extended (Sum.inr fresh) (Sum.inl column))
      (Matrix.of fun _ _ ↦ corner) := by
    ext i j
    cases i with
    | inl sourceRow =>
        cases j with
        | inl column =>
            rw [Matrix.fromBlocks_apply₁₁]
            exact hOld sourceRow column
        | inr fresh =>
            rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
            exact hZero sourceRow fresh
    | inr freshRow =>
        cases j with
        | inl column =>
            rw [Matrix.fromBlocks_apply₂₁]
            rfl
        | inr freshColumn =>
            rw [Matrix.fromBlocks_apply₂₂]
            exact hCorner freshRow freshColumn
  rw [hBlocks, Matrix.det_fromBlocks_zero₁₂]
  congr 1
  exact Matrix.det_unique _

/-- **The subdivision step.**  One target column is cut in two and one stable
row is cut in two.  The hypotheses are exactly what the geometry supplies:

* `hOld` -- an unsplit row sees the retained half of the cut column exactly as
  it saw the whole column, because every block it had over the old occurrence
  becomes a block over that half;
* `hDup` -- and it sees the fresh half the same way, so the two halves give
  identical columns outside the split row;
* `hSplitOld`, `hSplitNew` -- the two halves of the split row add up to the old
  row, on every column.

The conclusion is that the determinant is multiplied by the *defect*
`δ = A(h₂, e') - A(h₂, e'')`, the failure of the second half of the split row to
see the two halves of the cut column equally.  Geometrically `δ = ±1 / m(β)`
for the block `β` in whose interior the subdivision point was chosen, so it is
nonzero exactly when the attachment point is interior to a block. -/
theorem det_subdivision (old : Matrix index index ℚ)
    (subdivided : Matrix (index ⊕ Unit) (index ⊕ Unit) ℚ)
    (splitRow splitColumn : index)
    (hOld : ∀ sourceRow, sourceRow ≠ splitRow → ∀ column,
      subdivided (Sum.inl sourceRow) (Sum.inl column) = old sourceRow column)
    (hDup : ∀ sourceRow, sourceRow ≠ splitRow →
      subdivided (Sum.inl sourceRow) (Sum.inr ()) = old sourceRow splitColumn)
    (hSplitOld : ∀ column,
      subdivided (Sum.inl splitRow) (Sum.inl column) +
        subdivided (Sum.inr ()) (Sum.inl column) = old splitRow column)
    (hSplitNew :
      subdivided (Sum.inl splitRow) (Sum.inr ()) +
        subdivided (Sum.inr ()) (Sum.inr ()) = old splitRow splitColumn) :
    subdivided.det = old.det *
      (subdivided (Sum.inr ()) (Sum.inr ()) -
        subdivided (Sum.inr ()) (Sum.inl splitColumn)) := by
  classical
  set defect := subdivided (Sum.inr ()) (Sum.inr ()) -
    subdivided (Sum.inr ()) (Sum.inl splitColumn) with hdefect
  set columnCleared := subdivided.updateCol (Sum.inr ())
    (fun row ↦ subdivided row (Sum.inr ()) +
      (-1 : ℚ) • subdivided row (Sum.inl splitColumn)) with hcolumnCleared
  have hdetColumn : columnCleared.det = subdivided.det :=
    Matrix.det_updateCol_add_smul_self subdivided (by simp) (-1)
  set rowCleared := columnCleared.updateRow (Sum.inl splitRow)
    (columnCleared (Sum.inl splitRow) + (1 : ℚ) • columnCleared (Sum.inr ()))
    with hrowCleared
  have hdetRow : rowCleared.det = columnCleared.det :=
    Matrix.det_updateRow_add_smul_self columnCleared (by simp) 1
  have hColumnOld : ∀ row column,
      columnCleared row (Sum.inl column) = subdivided row (Sum.inl column) := by
    intro row column
    rw [hcolumnCleared, Matrix.updateCol_apply, ite_eq_right (by simp)]
  have hColumnNew : ∀ row,
      columnCleared row (Sum.inr ()) = subdivided row (Sum.inr ()) -
        subdivided row (Sum.inl splitColumn) := by
    intro row
    rw [hcolumnCleared, Matrix.updateCol_apply, ite_eq_left rfl]
    ring
  have hRowOther : ∀ row, row ≠ Sum.inl splitRow → ∀ column,
      rowCleared row column = columnCleared row column := by
    intro row hrow column
    rw [hrowCleared, Matrix.updateRow_ne hrow]
  have hRowSplit : ∀ column,
      rowCleared (Sum.inl splitRow) column =
        columnCleared (Sum.inl splitRow) column +
          columnCleared (Sum.inr ()) column := by
    intro column
    rw [hrowCleared, Matrix.updateRow_self]
    simp
  have hextend := det_extend old rowCleared defect ?_ ?_ ?_
  · rw [← hdetColumn, ← hdetRow, hextend]
  · intro sourceRow column
    by_cases hsplit : sourceRow = splitRow
    · subst hsplit
      rw [hRowSplit, hColumnOld, hColumnOld, hSplitOld]
    · rw [hRowOther _ (by simpa using hsplit), hColumnOld, hOld _ hsplit]
  · intro sourceRow fresh
    cases fresh
    by_cases hsplit : sourceRow = splitRow
    · subst hsplit
      rw [hRowSplit, hColumnNew, hColumnNew]
      have h1 := hSplitNew
      have h2 := hSplitOld splitColumn
      linarith
    · rw [hRowOther _ (by simpa using hsplit), hColumnNew, hDup _ hsplit,
        hOld _ hsplit]
      ring
  · intro freshRow freshColumn
    cases freshRow
    cases freshColumn
    rw [hRowOther _ (by simp), hColumnNew, hdefect]

/-- **No pendant shortcut.**  If the fresh target column carries only dangling
source edges then no stable path crosses it, its corner is `0`, and the
extended matrix is singular.  So a seed really cannot be obtained by hanging a
pendant target edge off the wall. -/
theorem det_extend_eq_zero_of_corner_zero (old : Matrix index index ℚ)
    (extended : Matrix (index ⊕ Unit) (index ⊕ Unit) ℚ)
    (hOld : ∀ sourceRow column,
      extended (Sum.inl sourceRow) (Sum.inl column) = old sourceRow column)
    (hZero : ∀ sourceRow fresh,
      extended (Sum.inl sourceRow) (Sum.inr fresh) = 0)
    (hCorner : ∀ freshRow freshColumn,
      extended (Sum.inr freshRow) (Sum.inr freshColumn) = 0) :
    extended.det = 0 := by
  rw [det_extend old extended 0 hOld hZero hCorner, mul_zero]

/-- Nonsingularity is preserved by a pendant step with nonzero corner. -/
theorem det_extend_ne_zero (old : Matrix index index ℚ)
    (extended : Matrix (index ⊕ Unit) (index ⊕ Unit) ℚ) (corner : ℚ)
    (hOld : ∀ sourceRow column,
      extended (Sum.inl sourceRow) (Sum.inl column) = old sourceRow column)
    (hZero : ∀ sourceRow fresh,
      extended (Sum.inl sourceRow) (Sum.inr fresh) = 0)
    (hCorner : ∀ freshRow freshColumn,
      extended (Sum.inr freshRow) (Sum.inr freshColumn) = corner)
    (hOldDet : old.det ≠ 0) (hCornerNe : corner ≠ 0) : extended.det ≠ 0 := by
  rw [det_extend old extended corner hOld hZero hCorner]
  exact mul_ne_zero hOldDet hCornerNe

/-- Nonsingularity is preserved by a subdivision step with nonzero defect. -/
theorem det_subdivision_ne_zero (old : Matrix index index ℚ)
    (subdivided : Matrix (index ⊕ Unit) (index ⊕ Unit) ℚ)
    (splitRow splitColumn : index)
    (hOld : ∀ sourceRow, sourceRow ≠ splitRow → ∀ column,
      subdivided (Sum.inl sourceRow) (Sum.inl column) = old sourceRow column)
    (hDup : ∀ sourceRow, sourceRow ≠ splitRow →
      subdivided (Sum.inl sourceRow) (Sum.inr ()) = old sourceRow splitColumn)
    (hSplitOld : ∀ column,
      subdivided (Sum.inl splitRow) (Sum.inl column) +
        subdivided (Sum.inr ()) (Sum.inl column) = old splitRow column)
    (hSplitNew :
      subdivided (Sum.inl splitRow) (Sum.inr ()) +
        subdivided (Sum.inr ()) (Sum.inr ()) = old splitRow splitColumn)
    (hOldDet : old.det ≠ 0)
    (hDefect : subdivided (Sum.inr ()) (Sum.inr ()) ≠
      subdivided (Sum.inr ()) (Sum.inl splitColumn)) :
    subdivided.det ≠ 0 := by
  rw [det_subdivision old subdivided splitRow splitColumn hOld hDup hSplitOld
    hSplitNew]
  exact mul_ne_zero hOldDet (sub_ne_zero_of_ne hDefect)

end TripodSteps

end DraismaVargas.LocalCases.SeedDeterminant
