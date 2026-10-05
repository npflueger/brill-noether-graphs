module

public import DraismaVargas.LocalCases.M11SplitLeaves

@[expose] public section

/-!
# The common stable row of surviving M11 split occurrences

All new background occurrences are dangling. Any surviving new occurrences
therefore meet at the distinguished source vertex over the target leaf.
Its actual incidence count is two, so these occurrences have the same stable
class. This does not by itself prove existence of a surviving new occurrence or
identify its class with a prescribed retained wall row.
-/

namespace DraismaVargas.LocalCases.M11SplitRows

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 GlobalM11Arbitrary M11SourceCandidates M11RemoteCandidates M11SplitLeaves
open W4Assembly W4StableSource W2R1Target SecondEquation

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- The literal left endpoint of a newly assembled source occurrence. -/
theorem newSourceEdge_fst (candidate : BalancedGlobal.Candidate target degree data wall)
    (sheet : Fin degree) :
    (candidate.datum.sourceEnds (candidate.newSourceEdge sheet)).1 =
      candidate.datum.sourceEndpoint (oldVertex target wall) sheet :=
  congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
      candidate.contracts candidate.exterior) sheet)

/-- Every actual occurrence over the new target edge is the canonical
new-edge block of its own representative sheet. -/
theorem eq_newSourceEdge_of_target (candidate : BalancedGlobal.Candidate target degree data wall)
    (edge : candidate.datum.SourceEdge)
    (hTarget : edge.1.1 = occurrenceEquiv target wall candidate.right none) :
    edge = candidate.newSourceEdge edge.1.2 := by
  have hCanonical := edge.2
  rw [hTarget] at hCanonical
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_edgePartition_new] at hCanonical
  apply Subtype.ext
  exact Prod.ext hTarget hCanonical.symm

/-- On the distinguished block, the split's left canonical representative is
the old wall representative, regardless of the sheet chosen. -/
theorem split_left_repr_of_rel (partition : SheetPartition degree)
    (distinguished sheet : Fin degree) (hRel : partition.Rel distinguished sheet) :
    (LocalResolution.onBlock partition distinguished (splitResolutionAt partition distinguished)
      (backgroundResolution partition) (partition.repr sheet)).left.repr sheet =
      partition.repr distinguished := by
  rw [LocalResolution.onBlock_of_rel _ _ _ _ _ (hRel.trans (partition.rel_repr_right sheet))]
  exact hRel.symm

/-- The joined left endpoint is shared by every sheet of the distinguished
block, in the actual pasted candidate. -/
theorem left_endpoint_eq_of_split (candidate : BalancedGlobal.Candidate target degree data wall)
    (distinguished sheet : Fin degree)
    (hResolution : ∀ anchor, candidate.resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) distinguished
        (splitResolutionAt (data.vertexPartition wall) distinguished)
        (backgroundResolution (data.vertexPartition wall)) anchor)
    (hRel : (data.vertexPartition wall).Rel distinguished sheet) :
    candidate.datum.sourceEndpoint (oldVertex target wall) sheet =
      candidate.datum.sourceEndpoint (oldVertex target wall) distinguished := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  change (candidate.datum.vertexPartition (oldVertex target wall)).repr sheet =
    (candidate.datum.vertexPartition (oldVertex target wall)).repr distinguished
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_vertexPartition_old_wall]
  change (candidate.resolution ((data.vertexPartition wall).repr sheet)).left.repr sheet =
    (candidate.resolution ((data.vertexPartition wall).repr distinguished)).left.repr distinguished
  rw [hResolution, hResolution, split_left_repr_of_rel _ _ _ hRel,
    split_left_repr_of_rel _ _ _ (show (data.vertexPartition wall).Rel distinguished distinguished from rfl)]

/-- Surviving occurrences meeting at an actual degree-two source vertex
belong to the same stable class, including the case of equal occurrences. -/
theorem stablePath_eq_of_incident_card_two (data : GluingDatum target degree)
    (hConnected : data.Connected) (first second : NonDanglingEdge data)
    (vertex : data.SourceVertex) (hFirst : Incident data first.1 vertex)
    (hSecond : Incident data second.1 vertex)
    (hCard : Fintype.card (IncidentSourceEdge data vertex) = 2) :
    first.stablePath = second.stablePath := by
  by_cases hSame : first = second
  · rw [hSame]
  apply stablePath_eq_of_consecutive
  refine ⟨hSame, vertex, hFirst, hSecond, ?_⟩
  have hUpper := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data vertex
  have hPositive := ClassInjectivity.nonDanglingValency_ne_zero_of_incident data first.2 hFirst
  have hLower := NonDanglingValency.nonDanglingValency_eq_zero_or_two_le data hConnected vertex
  omega

theorem firstSplit_new_stablePath_eq (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (first second : Fin degree)
    (hFirst : ¬ IsDangling (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.newSourceEdge first))
    (hSecond : ¬ IsDangling (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.newSourceEdge second)) :
    NonDanglingEdge.stablePath
      ⟨(firstSplitPattern input profile hCard).candidate.newSourceEdge first, hFirst⟩ =
    NonDanglingEdge.stablePath
      ⟨(firstSplitPattern input profile hCard).candidate.newSourceEdge second, hSecond⟩ := by
  have hSelected (sheet : Fin degree)
      (hSurvives : ¬ IsDangling (firstSplitPattern input profile hCard).candidate.datum
        ((firstSplitPattern input profile hCard).candidate.newSourceEdge sheet)) :
      (data.vertexPartition wall).Rel block.1 sheet := by
    by_contra hBackground
    exact hSurvives (firstSplit_background_isDangling input profile hCard sheet hBackground)
  apply stablePath_eq_of_incident_card_two _ (firstSplit_valid input profile hCard).1 _ _
    ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint
      (oldVertex target wall) block.1)
  · exact Or.inl ((newSourceEdge_fst _ first).trans
      (left_endpoint_eq_of_split _ block.1 first (fun _ ↦ rfl) (hSelected first hFirst)))
  · exact Or.inl ((newSourceEdge_fst _ second).trans
      (left_endpoint_eq_of_split _ block.1 second (fun _ ↦ rfl) (hSelected second hSecond)))
  · exact (firstSplit_left_card input profile hCard block.1).trans
      ((ite_eq_left (show (data.vertexPartition wall).Rel block.1 block.1 from rfl)).trans hCard)

theorem secondSplit_new_stablePath_eq (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (first second : Fin degree)
    (hFirst : ¬ IsDangling (secondSplitPattern input profile hCard).candidate.datum
      ((secondSplitPattern input profile hCard).candidate.newSourceEdge first))
    (hSecond : ¬ IsDangling (secondSplitPattern input profile hCard).candidate.datum
      ((secondSplitPattern input profile hCard).candidate.newSourceEdge second)) :
    NonDanglingEdge.stablePath
      ⟨(secondSplitPattern input profile hCard).candidate.newSourceEdge first, hFirst⟩ =
    NonDanglingEdge.stablePath
      ⟨(secondSplitPattern input profile hCard).candidate.newSourceEdge second, hSecond⟩ := by
  have hSelected (sheet : Fin degree)
      (hSurvives : ¬ IsDangling (secondSplitPattern input profile hCard).candidate.datum
        ((secondSplitPattern input profile hCard).candidate.newSourceEdge sheet)) :
      ((swappedDatum profile hCard).vertexPartition wall).Rel block.1 sheet := by
    rw [swappedDatum_vertexPartition profile hCard]
    by_contra hBackground
    exact hSurvives (secondSplit_background_isDangling input profile hCard sheet hBackground)
  apply stablePath_eq_of_incident_card_two _ (secondSplit_valid input profile hCard).1 _ _
    ((secondSplitPattern input profile hCard).candidate.datum.sourceEndpoint
      (oldVertex target wall) block.1)
  · exact Or.inl ((newSourceEdge_fst _ first).trans
      (left_endpoint_eq_of_split _ block.1 first (fun _ ↦ rfl) (hSelected first hFirst)))
  · exact Or.inl ((newSourceEdge_fst _ second).trans
      (left_endpoint_eq_of_split _ block.1 second (fun _ ↦ rfl) (hSelected second hSecond)))
  · exact (secondSplit_left_card input profile hCard block.1).trans
      ((ite_eq_left (show (data.vertexPartition wall).Rel block.1 block.1 from rfl)).trans hCard)

/-- A sheetwise equality applies to arbitrary surviving occurrences in the
literal new target fibre, with no proposed row enumeration. -/
theorem new_fibre_stablePath_eq_of_sheetwise
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (hSheetwise : ∀ first second : Fin degree,
      ∀ (hFirst : ¬ IsDangling candidate.datum (candidate.newSourceEdge first))
        (hSecond : ¬ IsDangling candidate.datum (candidate.newSourceEdge second)),
      NonDanglingEdge.stablePath ⟨candidate.newSourceEdge first, hFirst⟩ =
        NonDanglingEdge.stablePath ⟨candidate.newSourceEdge second, hSecond⟩)
    (first second : NonDanglingEdge candidate.datum)
    (hFirst : first.1.1.1 = occurrenceEquiv target wall candidate.right none)
    (hSecond : second.1.1.1 = occurrenceEquiv target wall candidate.right none) :
    first.stablePath = second.stablePath := by
  have hFirstEq := eq_newSourceEdge_of_target candidate first.1 hFirst
  have hSecondEq := eq_newSourceEdge_of_target candidate second.1 hSecond
  have hFirstSurvives : ¬ IsDangling candidate.datum (candidate.newSourceEdge first.1.1.2) :=
    hFirstEq ▸ first.2
  have hSecondSurvives : ¬ IsDangling candidate.datum (candidate.newSourceEdge second.1.1.2) :=
    hSecondEq ▸ second.2
  have hFirstTyped : first = ⟨candidate.newSourceEdge first.1.1.2, hFirstSurvives⟩ :=
    Subtype.ext hFirstEq
  have hSecondTyped : second = ⟨candidate.newSourceEdge second.1.1.2, hSecondSurvives⟩ :=
    Subtype.ext hSecondEq
  exact (congrArg NonDanglingEdge.stablePath hFirstTyped).trans
    ((hSheetwise _ _ hFirstSurvives hSecondSurvives).trans
      (congrArg NonDanglingEdge.stablePath hSecondTyped).symm)

/-- The first split's actual surviving new fibre occupies at most one stable
row. Existence of that row and its match with a retained row are separate. -/
theorem firstSplit_new_fibre_stablePath_eq (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (first second : NonDanglingEdge (firstSplitPattern input profile hCard).candidate.datum)
    (hFirst : first.1.1.1 = occurrenceEquiv target wall
      (firstSplitPattern input profile hCard).candidate.right none)
    (hSecond : second.1.1.1 = occurrenceEquiv target wall
      (firstSplitPattern input profile hCard).candidate.right none) :
    first.stablePath = second.stablePath :=
  new_fibre_stablePath_eq_of_sheetwise _ (firstSplit_new_stablePath_eq input profile hCard)
    first second hFirst hSecond

/-- The same actual-row statement holds after the remote sheet swap. -/
theorem secondSplit_new_fibre_stablePath_eq (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (first second : NonDanglingEdge (secondSplitPattern input profile hCard).candidate.datum)
    (hFirst : first.1.1.1 = occurrenceEquiv target wall
      (secondSplitPattern input profile hCard).candidate.right none)
    (hSecond : second.1.1.1 = occurrenceEquiv target wall
      (secondSplitPattern input profile hCard).candidate.right none) :
    first.stablePath = second.stablePath :=
  new_fibre_stablePath_eq_of_sheetwise _ (secondSplit_new_stablePath_eq input profile hCard)
    first second hFirst hSecond

end DraismaVargas.LocalCases.M11SplitRows
