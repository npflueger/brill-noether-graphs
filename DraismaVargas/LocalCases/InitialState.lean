module

public import DraismaVargas.LocalCases.MatrixAtlas
public import DraismaVargas.LocalCases.SeedCandidate
public import DraismaVargas.LocalCases.SeedDeterminant

@[expose] public section

/-!
# Initial states of the semantic march

A march needs an actual inhabitant of
`SemanticAtlasMarch.State degree matrix baseStart baseFinish` to start from.
This module builds one from a seed and a full-dimensional presentation of its
cover. The initial states the Draisma--Vargas construction starts from use it:
`CaterpillarSeed.uniformInitialState` and
`CaterpillarGenericSeed.exists_genericInitialState`, fed with the
full-dimensional presentation `CaterpillarRows.fullDim`, give unconditional
initial states in every even genus, including a start generic for the whole
finite atlas.

## The two halves of a state

`SemanticAtlasMarch.State` is a `FiniteAtlasMarch.State` together with
`carriesPencil`.  The semantic half is supplied by
`SeedCandidate.Seed.carriesClearedPencil`: a seed, a **full-dimensional source
presentation** of its cover and a positive rational coordinate vector inhabit
`CarriesClearedPencil`.  What it does not supply is the matrix side -- *a chart
whose matrix is this presentation's and whose determinant is nonzero* -- and
that is `MatrixAtlas.encodePresentation`, whose defining equation is
`MatrixAtlas.atlasMatrix_encodePresentation`.

The payload's presentation slot is a
`FullDimensionalSource.FullDimensionalSourcePresentation`, because the
continuation of the march classifies the incoming cover through it and it
cannot be recovered from the state otherwise.  Every construction below
therefore takes the full-dimensional package, and `stateOfFullDimensional` is
the clean form: the matrix-side hypotheses `hNodup` and `hDet` are two of its
fields.

`FiniteAtlasMarch.State.initial` supplies the four bookkeeping fields
(`lastWallTime := -1`, `restartTime := 0` and the two strict inequalities) and
converts a plain `hstartMap` into the segment-valued `currentStart_map` at
time zero.  It does **not** choose the two base points, and the two map
conditions

```
currentStart_map  : (matrix label).mulVec currentStart =
                      segment baseStart baseFinish restartTime
currentFinish_map : (matrix label).mulVec currentFinish = baseFinish
```

are the whole content of the construction.  Both are discharged by choosing
rather than solving:

* `currentStart := fun _ ↦ 1` is the positive coordinate vector, and
  `baseStart` is *defined* as its image, so `hstartMap` is
  `atlasMatrix_presentationChart` and nothing else;
* `baseFinish` stays an arbitrary parameter and `currentFinish` is its
  preimage `FiniteAtlasMarch.chartCoordinates`, whose defining property
  `mulVec_chartCoordinates` is exactly `currentFinish_map`.  Nonsingularity of
  the chart matrix, which the encoder already demanded, is what makes the
  preimage available.

## The encoder's hypothesis

`MatrixAtlas.encodePresentation` needs `∀ row, (presentation.path row).Nodup`,
which is what bounds the entries of the length matrix and therefore places it
in the finite atlas.  `state` takes that hypothesis verbatim;
`stateOfDecomposes` is the same construction fed from
`PresentationDecomposition.Decomposes`, whose `nodup` field it is.  A
`TraversalPresentation.StrongPresentation` carries a `Decomposes` as a field,
so a strong presentation feeds the initial state as well as the completion of
a terminal face.

## A concrete instance, and why it is not a seed

§3 records the duplicate-freeness ingredients of a concrete instance, built on
the arm extension of `ResolutionM11`'s M-11 split local model with the
one-block arm path `[0]`: the old rows are the two-element fibres of a
discrete-edge degree-two cover (`fibre_nodup`), and the fresh row is a
singleton.  Such an instance is only a **witness that the interfaces compose**
-- seed, presentation, nodup, determinant, chart encoding, base points, state
-- and it is *not* the Draisma--Vargas seed: the source of `splitLocalDatum`
has genus zero (`ResolutionM11.splitLocalSource_genus`), whereas the seed the
Cools--Draisma recursion starts from is the genus-two theta cover recorded in
`SeedDeterminant`.  Nor does it carry a full-dimensional presentation: every
occurrence of a pendant arm over a singleton wall block dangles, while
`PresentationDecomposition.Decomposes` -- a theorem about the honest labelling
of a full-dimensional source -- forbids a displayed row from listing a
dangling occurrence.
-/

namespace DraismaVargas.LocalCases.InitialState

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.SeedCandidate

/-! ## 2.  A semantic state from an arbitrary seed -/

section General

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {target : CFGraph} {data : GluingDatum target degree}

/-- The universal-atlas chart label displaying the length matrix of a
presentation with duplicate-free rows and nonsingular matrix. -/
noncomputable def presentationChart
    (presentation : data.LengthMatrixPresentation coordinate)
    (hNodup : ∀ row, (presentation.path row).Nodup)
    (hDet : (LengthMatrixPresentation.matrix presentation).det ≠ 0) :
    MatrixAtlas.chart coordinate degree :=
  MatrixAtlas.encodePresentation presentation hNodup hDet

@[simp] theorem atlasMatrix_presentationChart
    (presentation : data.LengthMatrixPresentation coordinate)
    (hNodup : ∀ row, (presentation.path row).Nodup)
    (hDet : (LengthMatrixPresentation.matrix presentation).det ≠ 0) :
    MatrixAtlas.atlasMatrix (presentationChart presentation hNodup hDet) =
      LengthMatrixPresentation.matrix presentation :=
  MatrixAtlas.atlasMatrix_encodePresentation presentation hNodup hDet

/-- **The matrix half of the initial state.**  The starting coordinates are the
all-ones vector, the starting base point is its image, and the finishing
coordinates are the preimage of the arbitrary base endpoint under the
nonsingular chart matrix. -/
noncomputable def matrixState
    (presentation : data.LengthMatrixPresentation coordinate)
    (hNodup : ∀ row, (presentation.path row).Nodup)
    (hDet : (LengthMatrixPresentation.matrix presentation).det ≠ 0)
    (baseFinish : coordinate → ℚ) :
    FiniteAtlasMarch.State
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
      ((LengthMatrixPresentation.matrix presentation).mulVec fun _ ↦ (1 : ℚ))
      baseFinish :=
  FiniteAtlasMarch.State.initial
    (presentationChart presentation hNodup hDet) (fun _ ↦ (1 : ℚ))
    (FiniteAtlasMarch.chartCoordinates
      (MatrixAtlas.atlasMatrix (presentationChart presentation hNodup hDet))
      baseFinish)
    (fun _ ↦ one_pos)
    (by rw [atlasMatrix_presentationChart])
    (FiniteAtlasMarch.mulVec_chartCoordinates _
      (MatrixAtlas.atlasMatrix_det_ne_zero _) baseFinish)

@[simp] theorem matrixState_label
    (presentation : data.LengthMatrixPresentation coordinate)
    (hNodup : ∀ row, (presentation.path row).Nodup)
    (hDet : (LengthMatrixPresentation.matrix presentation).det ≠ 0)
    (baseFinish : coordinate → ℚ) :
    (matrixState presentation hNodup hDet baseFinish).label =
      presentationChart presentation hNodup hDet := rfl

@[simp] theorem matrixState_currentStart
    (presentation : data.LengthMatrixPresentation coordinate)
    (hNodup : ∀ row, (presentation.path row).Nodup)
    (hDet : (LengthMatrixPresentation.matrix presentation).det ≠ 0)
    (baseFinish : coordinate → ℚ) :
    (matrixState presentation hNodup hDet baseFinish).currentStart =
      fun _ ↦ (1 : ℚ) := rfl

/-- **A semantic march state from a seed.**  The seed supplies `carriesPencil`
through `Seed.carriesClearedPencil` at the all-ones coordinate vector; the
universal atlas supplies the chart; the base points are chosen so that the two
map conditions hold by construction.

`carriesPencil` carries a
`FullDimensionalSource.FullDimensionalSourcePresentation`, so `state` takes one
and asks that it display `presentation`.  Given `fullDim`, the two matrix
hypotheses are free -- `hDet` is `fullDim.det_ne_zero` and `hNodup` is
`fullDim.decomposes.nodup`, both rewritten along `hPresentation` -- so
`stateOfFullDimensional` below is the same construction with nothing but the
seed, the full-dimensional package and a `baseFinish`. -/
noncomputable def state (seed : Seed degree)
    (presentation : seed.candidate.datum.LengthMatrixPresentation coordinate)
    (hNodup : ∀ row, (presentation.path row).Nodup)
    (hDet : (LengthMatrixPresentation.matrix presentation).det ≠ 0)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation
      seed.candidate.datum coordinate)
    (hPresentation : fullDim.labelling.presentation = presentation)
    (baseFinish : coordinate → ℚ) :
    SemanticAtlasMarch.State degree
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
      ((LengthMatrixPresentation.matrix presentation).mulVec fun _ ↦ (1 : ℚ))
      baseFinish where
  toMatrixState := matrixState presentation hNodup hDet baseFinish
  carriesPencil := by
    have hPencil := seed.carriesClearedPencil fullDim (fun _ ↦ (1 : ℚ))
      fun _ ↦ one_pos
    rw [hPresentation,
      ← atlasMatrix_presentationChart presentation hNodup hDet] at hPencil
    exact hPencil

/-- The same construction fed from `PresentationDecomposition.Decomposes`,
whose `nodup` field is exactly what the encoder wants.  A
`TraversalPresentation.StrongPresentation` carries one as a field. -/
noncomputable def stateOfDecomposes (seed : Seed degree)
    (presentation : seed.candidate.datum.LengthMatrixPresentation coordinate)
    (hDecomposes : PresentationDecomposition.Decomposes presentation)
    (hDet : (LengthMatrixPresentation.matrix presentation).det ≠ 0)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation
      seed.candidate.datum coordinate)
    (hPresentation : fullDim.labelling.presentation = presentation)
    (baseFinish : coordinate → ℚ) :
    SemanticAtlasMarch.State degree
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
      ((LengthMatrixPresentation.matrix presentation).mulVec fun _ ↦ (1 : ℚ))
      baseFinish :=
  state seed presentation hDecomposes.nodup hDet fullDim hPresentation baseFinish

/-- **The state from a full-dimensional presentation alone.**  Both matrix-side
hypotheses of `state` are fields of the full-dimensional package, so a seed and
a `FullDimensionalSource.FullDimensionalSourcePresentation` of its cover are by
themselves a `SemanticAtlasMarch.State`.  The initial-state interface thus
consumes exactly what the payload carries, and nothing else. -/
noncomputable def stateOfFullDimensional (seed : Seed degree)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation
      seed.candidate.datum coordinate)
    (baseFinish : coordinate → ℚ) :
    SemanticAtlasMarch.State degree
      (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
      ((LengthMatrixPresentation.matrix fullDim.labelling.presentation).mulVec
        fun _ ↦ (1 : ℚ))
      baseFinish :=
  state seed fullDim.labelling.presentation fullDim.decomposes.nodup
    fullDim.det_ne_zero fullDim rfl baseFinish

end General

/-! ## 3.  Ingredients of a concrete instance

Everything above is hypothetical in a seed, a presentation of its cover with
duplicate-free rows, and a nonsingular length matrix.  The two facts below are
the duplicate-freeness ingredients of the arm extension of the M-11 split local
model: fibre rows of a discrete-edge degree-two cover, and the one-block arm
path. -/

section Concrete

open DraismaVargas.LocalCases.ResolutionM11

/-- The two blocks of a discrete-edge degree-two cover lying over one target
occurrence are distinct, so every row of a fibre presentation is
duplicate-free. -/
theorem fibre_nodup (target : CFGraph)
    (vertexPartition : target.V → SheetPartition 2) (edge : target.edges) :
    (SeedDeterminant.fibre target vertexPartition edge).Nodup := by
  have hNe : SeedDeterminant.fibreBlock target vertexPartition edge 0 ≠
      SeedDeterminant.fibreBlock target vertexPartition edge 1 := by
    intro hEqual
    have hSheet : (0 : Fin 2) = 1 := congrArg (fun block ↦ block.1.2) hEqual
    exact absurd hSheet (by decide)
  simpa [SeedDeterminant.fibre] using hNe

/-- **The one-block arm path.**  A single block over the arm.

Any duplicate-free nonempty list of sheets would serve: duplicate-freeness of
the arm path gives a duplicate-free fresh row, and nonemptiness is what a
nonsingular arm presentation needs.  The singleton is the shortest list meeting
both. -/
def splitLocalArmPath : List (Fin 2) := [0]

theorem splitLocalArmPath_ne_nil : splitLocalArmPath ≠ [] := by
  simp [splitLocalArmPath]

theorem splitLocalArmPath_nodup : splitLocalArmPath.Nodup :=
  List.nodup_singleton _

end Concrete

end DraismaVargas.LocalCases.InitialState
