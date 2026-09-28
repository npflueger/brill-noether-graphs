import DraismaVargas.LocalCases.TargetRelabelStable
import DraismaVargas.LocalCases.StableGraphFullDimensional
import Utilities.Subdivision.GraphIsoLaplacianEquiv

/-!
# Full-dimensional presentations under actual target and sheet relabelling

Transport honest coordinates along the occurrence-induced stable-row and
target-edge equivalences. The complete matrices are equal, not merely equal
up to a sign or a separately assumed row permutation. Validity, genus,
trivalence and path ends then reconstruct the full-dimensional presentation.
These are conditional transport constructors, not an incoming classification.
-/

namespace DraismaVargas.LocalCases.RelabelFullDimensional

open Utilities DraismaVargas.Infrastructure GluingTransport
open W4StableSource FullDimensionalSource StableSourceMatrix

variable {G H : CFGraph} {degree : ℕ} {coordinate : Type*}
  [Fintype coordinate] [DecidableEq coordinate]

noncomputable def targetLabelling (φ : CFGraphIso G H) (data : GluingDatum G degree)
    (hConnected : data.Connected) (labelling : StableLengthMatrixLabelling data coordinate) :
    StableLengthMatrixLabelling (transport φ data) coordinate where
  targetEdge := labelling.targetEdge.trans (edgeEquiv φ)
  row := (TargetRelabelStable.stablePathEquiv φ data hConnected).symm.trans labelling.row

theorem target_matrix_eq (φ : CFGraphIso G H) (data : GluingDatum G degree)
    (hConnected : data.Connected) (labelling : StableLengthMatrixLabelling data coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (targetLabelling φ data hConnected labelling).presentation =
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation := by
  ext row column
  rw [labelling_matrix_eq, labelling_matrix_eq]
  change matrix (transport φ data)
    (TargetRelabelStable.stablePathEquiv φ data hConnected (labelling.row.symm row))
    (edgeEquiv φ (labelling.targetEdge column)) = _
  exact TargetRelabelStable.matrix_map φ data hConnected _ _

/-- Every structural field and the honest determinant are derived from the
given full-dimensional source and its actual target isomorphism. -/
noncomputable def targetPresentation (φ : CFGraphIso G H) {data : GluingDatum G degree}
    (source : FullDimensionalSourcePresentation data coordinate) :
    FullDimensionalSourcePresentation (transport φ data) coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence source
    (TargetRelabelStable.graphEquivalence φ data source.valid.1)
    (valid_transport φ data source.valid)
    (φ.toLaplacianEquiv.graphConnected source.targetConnected)
    (φ.toLaplacianEquiv.genus_eq.trans source.targetGenus)
    φ.toLaplacianEquiv.cardEdges_eq
    (TargetRelabelPruning.sourceGraphLaplacianEquiv φ data).genus_eq
    (targetLabelling φ data source.valid.1 source.labelling)
    (by rw [target_matrix_eq]; exact source.det_ne_zero)

noncomputable def sheetLabelling {data : GluingDatum G degree}
    (relabeling : data.SheetRelabeling) (hConnected : data.Connected)
    (labelling : StableLengthMatrixLabelling data coordinate) :
    StableLengthMatrixLabelling relabeling.apply coordinate where
  targetEdge := labelling.targetEdge
  row := (SheetRelabelStable.stablePathEquiv relabeling hConnected).symm.trans labelling.row

theorem sheet_matrix_eq {data : GluingDatum G degree}
    (relabeling : data.SheetRelabeling) (hConnected : data.Connected)
    (labelling : StableLengthMatrixLabelling data coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (sheetLabelling relabeling hConnected labelling).presentation =
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation := by
  ext row column
  rw [labelling_matrix_eq, labelling_matrix_eq]
  change matrix relabeling.apply
    (SheetRelabelStable.stablePathEquiv relabeling hConnected (labelling.row.symm row))
    (labelling.targetEdge column) = _
  exact SheetRelabelStable.matrix_map relabeling hConnected _ _

/-- Compatible sheet permutations preserve full-dimensionality in the
induced coordinates, including the incoming determinant's exact sign. -/
noncomputable def sheetPresentation {data : GluingDatum G degree}
    (relabeling : data.SheetRelabeling)
    (source : FullDimensionalSourcePresentation data coordinate) :
    FullDimensionalSourcePresentation relabeling.apply coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence source
    (StableGraphIncidence.sheetRelabel relabeling source.valid.1)
    (relabeling.valid source.valid) source.targetConnected source.targetGenus rfl
    relabeling.sourceGraphLaplacianEquiv.genus_eq
    (sheetLabelling relabeling source.valid.1 source.labelling)
    (by rw [sheet_matrix_eq]; exact source.det_ne_zero)

end DraismaVargas.LocalCases.RelabelFullDimensional
