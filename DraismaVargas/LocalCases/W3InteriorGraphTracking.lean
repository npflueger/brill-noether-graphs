module

public import DraismaVargas.LocalCases.InteriorGraphTracking
public import DraismaVargas.LocalCases.W3FourClosureFinal

@[expose] public section

/-!
# Recovering W3 row tracking before the final existential packaging

This is a source-facing intermediate, not a tracked final W3 exit. Matrix
nonsingularity recovers a row dictionary only when the actual natural matrices
and target occurrence map have already been proved compatible. An arbitrary
stable-incidence equivalence does not supply that matrix compatibility.

`exists_matched_tracking` consumes the existing incoming normalization and
retains the same presentation together with the actual target/partition
incidence dictionary and its recovered row equation. The source census and
placement dichotomy are the existing inputs of that producer, not replacement
matching assumptions. `columnData_honestLabelling_row` then recovers the
literal witness supplied by each concrete regrown-column construction.

The integration loss at this level is precise: `MemberCertificates` stores its
incidence dictionary independently of existential `HonestFigure28.honest`;
`FamilyMatching` retains only matrix and wall-column equalities; and the
final exit rematches the incoming member for its graph certificate. To track
the final exit one must retain the concrete column-to-dictionary row equations
through the anchored construction and strengthen the actual family-matching
producer with that same-candidate dictionary. No change to those APIs, no
outgoing row compatibility hypothesis at the final producer, and no completed
march invariant is asserted here. Vargas, Part II, Section 4 is the
source-facing distinction between these type-preserving interior crossings and
genuine type changes.
-/

namespace DraismaVargas.LocalCases.W3InteriorGraphTracking

open DraismaVargas.Infrastructure
open W4StableSource FullDimensionalSource InteriorGraphTracking

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {target otherTarget : CFGraph} {degree otherDegree : ℕ}
  {data : GluingDatum target degree} {other : GluingDatum otherTarget otherDegree}

/-- No two rows of an actual nonsingular square matrix coincide. -/
theorem matrix_row_injective (M : Matrix coordinate coordinate ℚ) (hDet : M.det ≠ 0) :
    Function.Injective M := by
  intro i j h
  by_contra hne
  exact hDet (Matrix.det_zero_of_row_eq hne h)

/-- An honest full-dimensional presentation makes the natural stable rows
distinct, independently of its choice of finite coordinate order. -/
theorem natural_row_injective_of_labelling
    (labelling : StableLengthMatrixLabelling data coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    Function.Injective (StableSourceMatrix.matrix data) := by
  intro r s h
  apply labelling.row.injective
  apply matrix_row_injective _ hDet
  funext c
  simp only [StableSourceMatrix.labelling_matrix_eq, Equiv.symm_apply_apply]
  exact congrFun h (labelling.targetEdge c)

theorem natural_row_injective (fd : FullDimensionalSourcePresentation data coordinate) :
    Function.Injective (StableSourceMatrix.matrix data) :=
  natural_row_injective_of_labelling fd.labelling fd.det_ne_zero

/-- The actual natural matrix dictionary, together with the literal column
dictionary, forces the coordinate row equation. No graph witness is inferred
from matrix equality. -/
theorem row_eq_of_natural_matrix_map
    (fd : FullDimensionalSourcePresentation data coordinate)
    (outFD : FullDimensionalSourcePresentation other coordinate)
    (rows : StablePath data ≃ StablePath other)
    (columns : target.edges ≃ otherTarget.edges)
    (hColumns : outFD.labelling.targetEdge = fd.labelling.targetEdge.trans columns)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix outFD.labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
    (hNatural : ∀ r e, StableSourceMatrix.matrix other (rows r) (columns e) =
      StableSourceMatrix.matrix data r e) :
    outFD.labelling.row = rows.symm.trans fd.labelling.row := by
  ext r
  apply fd.labelling.row.symm.injective
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  apply natural_row_injective fd
  funext e
  have h := congrFun (congrFun hMatrix (outFD.labelling.row r))
    (fd.labelling.targetEdge.symm e)
  simp only [StableSourceMatrix.labelling_matrix_eq, Equiv.symm_apply_apply,
    hColumns, Equiv.trans_apply, Equiv.apply_symm_apply] at h
  exact h.symm.trans (by simpa using hNatural (rows.symm r) e)

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- Unpack the SAME normalized presentation and recover its exact geometric
row equation from the already-certified natural matrix and occurrence maps. -/
theorem matched_tracking_of_normalized
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fd graph label)
    {iso : Utilities.CFGraphIso target otherTarget}
    {other : GluingDatum otherTarget degree}
    {hVertices : ∀ v, ((GluingTransport.transport iso data).vertexPartition v).SameBlocks
      (other.vertexPartition v)}
    {hEdges : ∀ e, ((GluingTransport.transport iso data).edgePartition e).SameBlocks
      (other.edgePartition e)}
    (hNorm : W3Nd2IncomingMemberMatching.NormalizedAgainst data fd iso other hVertices hEdges) :
    ∃ outFD : FullDimensionalSourcePresentation other coordinate,
      GluingDatum.LengthMatrixPresentation.matrix outFD.labelling.presentation =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation ∧
      outFD.labelling.targetEdge = fd.labelling.targetEdge.trans (GluingTransport.edgeEquiv iso) ∧
      outFD.labelling.row =
        (TargetPartitionNormalization.graphEquivalence iso data other hVertices hEdges
          fd.connected).row.symm.trans fd.labelling.row ∧
      Nonempty (Tracks outFD graph label) := by
  obtain ⟨sheets, hApply, outFD, hEdge, hMatrix, hOccurrence, hNatural⟩ := hNorm
  have hRows := row_eq_of_natural_matrix_map fd outFD
    (TargetPartitionNormalization.stablePathEquiv iso data other hVertices hEdges fd.connected)
    (GluingTransport.edgeEquiv iso) hEdge hMatrix hNatural
  rw [← TargetPartitionNormalization.graphEquivalence_row] at hRows
  exact ⟨outFD, hMatrix, hEdge, hRows, ⟨throughIncidence current outFD _ hRows⟩⟩

open GraphContraction GluingContraction ContractionRamification WallDegeneration
open ThirdEquation W3R1SourceProfile TargetExpansion
open W3Nd2IncomingTargetPlacement (divalentOccurrence)
open W3FourIncomingCensus (WallMember)
open W3ShiftIncomingMatching (SelectedCensus)

/-- The actual W3 matching producer, with tracking on its SAME identified
member. The census inputs here are those supplied by the final source-facing
anchoring producer; no membership or graph/row matching is assumed. -/
theorem exists_matched_tracking
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fd graph label)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (input : W3SourceInput (contractDatum data hc hab hOne) star)
    (members : Fin 3 → WallMember (contractDatum data hc hab hOne) ⟨a, hab⟩
      input.distinguishedBlock.1)
    (hDichotomy : ∃ index : Fin 3,
      divalentOccurrence data hc hab hOne fd star = (members index).isolated)
    (hCensus : ∀ index : Fin 3,
      divalentOccurrence data hc hab hOne fd star = (members index).isolated →
      SelectedCensus data hc hab hOne star input (members index).selectedLeft
        (members index).selectedRight (members index).selectedNew) :
    ∃ index : Fin 3,
      divalentOccurrence data hc hab hOne fd star = (members index).isolated ∧
      ∃ outFD : FullDimensionalSourcePresentation (members index).candidate.datum coordinate,
        GluingDatum.LengthMatrixPresentation.matrix outFD.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation ∧
        outFD.labelling.targetEdge.symm
            (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
              (members index).candidate.right none) = fd.labelling.targetEdge.symm contracted ∧
        ∃ certificate : StableGraphIncidence.Equivalence data (members index).candidate.datum,
          outFD.labelling.row = certificate.row.symm.trans fd.labelling.row ∧
          Nonempty (Tracks outFD graph label) := by
  classical
  obtain ⟨index, hIndex, hColumns, hNorm⟩ :=
    W3FourIncomingMatching.exists_member_normalization data hc hab hOne fd hForest star
      input members hDichotomy hCensus
  obtain ⟨outFD, hMatrix, hEdge, hRows, hTrack⟩ :=
    matched_tracking_of_normalized data fd current hNorm
  refine ⟨index, hIndex, outFD, hMatrix, ?_, _, hRows, hTrack⟩
  rw [hEdge, ← hColumns none, Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rfl

open W3FourRegrownColumn W3FourHonestBalance

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- At a nonsingular member, existential honesty cannot silently select a
different row ordering from a proved literal natural-matrix witness. -/
theorem honestLabelling_row_eq
    {wall : target.V} {base : GluingDatum target degree}
    {candidate : BalancedGlobal.Candidate target degree base wall}
    {presentation : candidate.datum.LengthMatrixPresentation (Option target.edges)}
    (honest : IsHonest candidate presentation)
    (literalRows : Option target.edges ≃ StablePath candidate.datum)
    (hLiteral : GluingDatum.LengthMatrixPresentation.matrix presentation =
      (StableSourceMatrix.matrix candidate.datum).submatrix literalRows
        (occurrenceEquiv target wall candidate.right))
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix presentation).det ≠ 0) :
    (honestLabelling honest).row = literalRows.symm := by
  have hHonestDet := honestLabelling_det_ne_zero honest hDet
  have hInjective : Function.Injective (StableSourceMatrix.matrix candidate.datum) :=
    natural_row_injective_of_labelling (honestLabelling honest) hHonestDet
  have hChosen : honest.choose = literalRows := by
    ext r
    apply hInjective
    funext edge
    have h := congrFun (congrFun (honest.choose_spec.symm.trans hLiteral) r)
      ((occurrenceEquiv target wall candidate.right).symm edge)
    simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using h
  exact congrArg Equiv.symm hChosen

/-- The concrete column producer's geometric row witness survives passage
through `IsHonest` at every nonsingular member. -/
theorem columnData_honestLabelling_row
    {wall : target.V} {geometry : W3FourClosure.FourStarGeometry data wall}
    {labelling : W4StableSource.StablePathLabelling data}
    (cd : ColumnData data wall geometry labelling)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      (soloPresentation cd.memberColumn
        (W3FourLimitRows.stableRowPath labelling))).det ≠ 0) :
    (honestLabelling cd.isHonest).row = cd.rowEquiv.symm :=
  honestLabelling_row_eq cd.isHonest cd.rowEquiv cd.presented_matrix_submatrix hDet

/-- Expanded form: the recovered row coordinates follow the actual gauge
row map and the actual regrown member's row descent. -/
theorem columnData_honestLabelling_row_geometric
    {wall : target.V} {geometry : W3FourClosure.FourStarGeometry data wall}
    {labelling : W4StableSource.StablePathLabelling data}
    (cd : ColumnData data wall geometry labelling)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix
      (soloPresentation cd.memberColumn
        (W3FourLimitRows.stableRowPath labelling))).det ≠ 0) :
    (honestLabelling cd.isHonest).row =
      (cd.gauge.row.trans cd.rowData.stablePathEquiv).symm.trans labelling.row := by
  rw [columnData_honestLabelling_row cd hDet]
  rfl

end DraismaVargas.LocalCases.W3InteriorGraphTracking

