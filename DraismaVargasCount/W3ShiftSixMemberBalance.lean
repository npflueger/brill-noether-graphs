import DraismaVargasCount.W3ShiftMultiplicityBalance
import DraismaVargas.LocalCases.SheetRelabelIncidence
import DraismaVargas.LocalCases.W3ShiftClosure

/-!
# The three actual Equation (3) shift pairs

Equation (3) of Draisma--Vargas Part I (arXiv:1909.12924) is the balance in case
`{w3-r1-nd3-t2-(a>k4)}`, over three shrink/grow pairs like the one in that paper's Figure 29.
This file packages the two branch swaps used to construct one Figure 29 pair
without forgetting their stable-incidence dictionary.  Applying the package to
the largest, first and second orientations is the geometric six-member family
of Equation (3); in particular it does not assume three unrelated shrink sheets.
The package also retains the matrix identity supplied by the two actual sheet
relabelings. Stable incidence alone would not imply this identity. The six-term
signed-multiplicity balance is proved separately in `W3ShiftSixMemberMultiplicity`.
-/

namespace DraismaVargas.Count.W3ShiftSixMemberBalance

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open W4Assembly ThirdEquation W3R1SourceProfile
open W3ShiftSourceCandidates W3ShiftClosure
open W3FourDisjointness

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

/-- One actual shift pair, on the branch-swapped gauge copy which supplies its
shrink sheet, together with the stable-incidence dictionary from the common
ungauged wall datum. -/
structure PairPackage (shift : ShiftProfile input) where
  base : GluingDatum target degree
  gaugeInput : W3SourceInput base star
  gaugeShift : ShiftProfile gaugeInput
  shrink : ShrinkData gaugeShift
  copy : GaugeCopy input shift gaugeInput gaugeShift
  incidence : StableGraphIncidence.Equivalence data base
  /-- The actual relabeling dictionary preserves every original target column. -/
  matrix_map : ∀ (path : W4StableSource.StablePath data) (place : target.edges),
    StableSourceMatrix.matrix base (incidence.row path) place =
      StableSourceMatrix.matrix data path place

/-- The two clearing swaps construct an actual pair and, because they are
literal sheet relabellings, retain its dictionary to the common wall datum. -/
theorem exists_pairPackage (shift : ShiftProfile input)
    (hRetained : RetainedBelow shift)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    Nonempty (PairPackage shift) := by
  let endpoint := data.vertexPartition wall
  have hEndpoint : endpoint.Refines (data.vertexPartition wall) :=
    SheetPartition.Refines.refl _
  obtain ⟨permFirst, hFixFirst, permSecond, hFixSecond, gaugeInput, gaugeShift,
      copy, hSheet⟩ :=
    exists_gaugeCopy_shrinkSheet_endpoint input shift endpoint hEndpoint
      (StableLocalProperties.refines_of_mem_incidentEdges data shift.firstTarget_mem)
      (StableLocalProperties.refines_of_mem_incidentEdges data shift.secondTarget_mem)
      (shift.movingAnchor_wall_rel.symm.trans shift.firstAnchor_wall_rel)
      (shift.movingAnchor_wall_rel.symm.trans shift.secondAnchor_wall_rel)
      (by simpa [endpoint] using hRetained.1)
      (by simpa [endpoint] using hRetained.2) hConnected hGenus
  obtain ⟨shrink⟩ := exists_shrinkData gaugeShift hSheet
  let firstRelabel := branchSwapOfPerm data wall
    (TargetSeparation.farEndpoint wall shift.firstTarget)
    (TargetSeparation.farEndpoint_ne
      (mem_incidentEdges_ends shift.firstTarget_mem))
    permFirst (fun sheet ↦ hEndpoint.rel (hFixFirst sheet))
  let dataOne := firstRelabel.apply
  let secondRelabel := branchSwapOfPerm dataOne wall
    (TargetSeparation.farEndpoint wall shift.secondTarget)
    (TargetSeparation.farEndpoint_ne
      (mem_incidentEdges_ends shift.secondTarget_mem))
    permSecond (fun sheet ↦
      (refines_clearData_wall data shift.firstTarget shift.firstTarget_mem endpoint
        hEndpoint permFirst hFixFirst).rel (hFixSecond sheet))
  let hIncidence : StableGraphIncidence.Equivalence data secondRelabel.apply :=
    (SheetRelabelIncidence.equivalence firstRelabel input.valid.1).trans
      (SheetRelabelIncidence.equivalence secondRelabel
        (firstRelabel.valid input.valid).1)
  refine ⟨⟨_, gaugeInput, gaugeShift, shrink, copy, hIncidence, ?_⟩⟩
  intro path place
  change StableSourceMatrix.matrix secondRelabel.apply
    (SheetRelabelStable.stablePathEquiv secondRelabel (firstRelabel.valid input.valid).1
      (SheetRelabelStable.stablePathEquiv firstRelabel input.valid.1 path)) place = _
  rw [SheetRelabelStable.matrix_map, SheetRelabelStable.matrix_map]

/-- The three source orientations in Equation (3), ordered as
`(k₄−1,k₄+1)`, `(k₂−1,k₂+1)`, `(k₃−1,k₃+1)`. -/
noncomputable def orientation (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    Fin 3 → ShiftProfile input :=
  ![shiftProfileLargest profile directions largest_lt,
    shiftProfileFirst profile directions largest_lt,
    shiftProfileSecond profile directions largest_lt]

/-- **The actual six-member geometry of Equation (3).**  One package is
constructed for each of the three source directions; each package contains its
shrink and grow member over one gauge base and a dictionary from the same
ungauged wall datum.  Thus the shrink sheets are conclusions of the source
construction, not three caller-supplied receipts. -/
theorem exists_sixPackages
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    Nonempty (∀ direction : Fin 3,
      PairPackage (orientation profile directions largest_lt direction)) := by
  have hRetained := retainedBelow_of_largest_lt profile directions largest_lt
  have hPair (direction : Fin 3) :
      Nonempty (PairPackage (orientation profile directions largest_lt direction)) := by
    fin_cases direction
    · exact exists_pairPackage _ hRetained.1 hConnected hGenus
    · exact exists_pairPackage _ hRetained.2.1 hConnected hGenus
    · exact exists_pairPackage _ hRetained.2.2 hConnected hGenus
  exact ⟨fun direction ↦ Classical.choice (hPair direction)⟩

end DraismaVargas.Count.W3ShiftSixMemberBalance
