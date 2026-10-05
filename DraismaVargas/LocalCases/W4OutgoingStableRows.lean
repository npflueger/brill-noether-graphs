module

public import DraismaVargas.LocalCases.W4OutgoingSurvival
public import DraismaVargas.LocalCases.ResolutionStableIncidence
public import DraismaVargas.LocalCases.StableSourceMatrix

@[expose] public section

/-!
# Occurrence-induced stable rows and branch incidences for the outgoing W4
candidates

`W4StableGraph` and `W4OutgoingSurvival` settle, for each of the three actual
members of an `AuxR0SourceInput`'s semantic family, source-genus preservation,
the exact pruning of retained old occurrences, the complete new-occurrence
census, and the literal surviving valencies at both expanded endpoints.  What
they do **not** supply is the identification of the stable rows and of the
stable incidence graph across the wall.  That is what this module proves, at
the level of literal quotient-source occurrences:

* `stablePathEquiv` — the stable-row equivalence induced by retaining an actual
  surviving incoming occurrence, together with its explicit reverse assignment
  `stablePathDescend` (`stablePathDescend_lift`).  Injectivity comes from that
  geometric left inverse, never from a row count.
* `equivalence` — a `StableGraphIncidence.Equivalence` between the incoming
  wall datum and each outgoing candidate: a bijection `branchVertexEquiv` of
  surviving branch vertices together with `stablePathEquiv`, preserving
  `incidenceCount` at every branch/row pair.  At the trivalent nd3 branch a row
  carried by two of the three incoming occurrences is carried twice on the
  outgoing side as well (`incidenceCount_nd3_branch`).
* `matrix_retained` — every column of the honest natural stable-length matrix
  `StableSourceMatrix.matrix` of an outgoing candidate other than the regrown
  one is literally the incoming wall column, read through `stablePathEquiv`.
  This is the limit-matrix lemma of Draisma--Vargas Part I
  (`lemma-limit-matrix-change`) for the W4 wall (Case {w4}), in the up
  direction and without a compatible-labelling hypothesis.

Nothing here evaluates the regrown column, identifies
`AuxR0SourceInput.presentedFamily`'s presented matrices with the natural
matrices, or proves Equation (1); `mem_occurrences_new_iff` only pins down
which occurrences that column is supported on.  Those are in
`W4OutgoingLimitMatrix` and the modules after it.

**No path list is read.**  `AuxR0SourceInput.presentedFamily` carries raw path
lists and algebraic determinant receipts; they are not used, and no statement
below is a cardinality bijection.  Rows are the `Consecutive` quotient of
literal surviving occurrences, branch vertices are literal quotient-source
vertices of surviving valency at least three, and every incidence is counted
with multiplicity.

**Which side of the wall bridge.**  Everything is stated for an
`AuxR0SourceInput`, the codimension-one wall datum, exactly as
`W4OutgoingSurvival` is; no `FullDimensionalSourcePresentation` appears, so
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput` is not in
play.  The hypotheses are the five fields of `AuxR0SourceInput` and nothing
else: no distinctness, no path-end, and no extra graph receipt is added to any
statement, so the results hold whenever that input does — for instance for the
inputs produced by `AuxR0SourceInput.ofChangeMinimalExpansion`.

## What the three source pictures contribute

Above a dangling wall block both expanded endpoints are isolated; above an nd2
block the two canonical branch occurrences already share one incoming row
(`nd2_old_stablePath_eq`, from the picture's own connectedness field) and keep
it after resolution, either by staying directly consecutive (same-side
pairing) or through the single surviving regrown occurrence (opposite-side
pairing); above an nd3 block the incoming wall vertex is trivalent, so it is no
junction at all, and its outgoing image is the trivalent endpoint carrying the
two remaining branches and the regrown occurrence.

Source: Draisma--Vargas Part I, the subsection on inherited properties for the
induced labellings and the limit matrix (`lemma-limit-matrix-change`), and
Case {aux-r0} for the auxiliary nd2 and nd3 cases.
-/

namespace DraismaVargas.LocalCases.W4OutgoingStableRows

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 W4Assembly GlobalW4 W4StableSource W4StableGraph
open W4SourceClassification ResolutionAwayFromWall W4OutgoingSurvival
open StableGraphIncidence StablePathCount StableSourceMatrix

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-! ## The old wall vertex of a source vertex above the wall -/

/-- Every sheet lies in its own old wall block. -/
theorem rel_ofSheet (data : GluingDatum target degree) (wall : target.V)
    (sheet : Fin degree) :
    (data.vertexPartition wall).Rel (WallBlock.ofSheet data wall sheet).1
      sheet :=
  (WallBlock.ofSheet_eq_iff_rel data wall (WallBlock.ofSheet data wall sheet)
    sheet).1 rfl


section Old

variable {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall}

/-- Every quotient-source vertex above the W4 wall is the source vertex of an
actual old wall block. -/
theorem exists_wallBlock_sourceVertex (data : GluingDatum target degree)
    (wall : target.V) (vertex : data.SourceVertex) (hAt : vertex.1.1 = wall) :
    ∃ sourceBlock : WallBlock data wall,
      WallBlock.sourceVertex data wall sourceBlock = vertex := by
  refine ⟨⟨vertex.1.2, ?_⟩, ?_⟩
  · exact hAt ▸ vertex.2
  · exact (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr
      ⟨hAt.symm, rfl⟩

/-- A surviving occurrence at the old wall vertex comes from one of the four
star branches and lies in that block. -/
theorem old_survivor_info (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (sourceBlock : WallBlock data wall) (edge : data.SourceEdge)
    (hIncident : Incident data edge
      (WallBlock.sourceVertex data wall sourceBlock)) :
    WallBlock.ofSheet data wall edge.1.2 = sourceBlock ∧
      ∃ label : Fin 4, star.edge label = edge.1.1 := by
  obtain ⟨hMem, hBlock⟩ :=
    (incident_wallBlock_sourceVertex_iff data sourceBlock edge).mp hIncident
  exact ⟨hBlock, star.exists_edge_eq edge.1.1 hMem⟩

/-- **Dangling wall block.**  Nothing survives at its old wall vertex. -/
theorem dangling_not_incident (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge)
    (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge
      (WallBlock.sourceVertex data wall sourceBlock)) : False := by
  obtain ⟨hBlock, label, hLabel⟩ :=
    old_survivor_info data star sourceBlock edge hIncident
  exact hSurvives (old_dangling edge label hBlock hLabel)

/-- **nd2 wall block.**  Every old survivor at its wall vertex is one of the
two canonical branch occurrences. -/
theorem nd2_old_survivor_eq {sourceBlock : WallBlock data wall} {block : Nd2Block}
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge
      (WallBlock.sourceVertex data wall sourceBlock)) :
    edge = data.sourceEdge (star.edge block.first) sourceBlock.1 ∨
      edge = data.sourceEdge (star.edge block.second) sourceBlock.1 := by
  obtain ⟨hBlock, hLabel⟩ :=
    old_survivor_info data star sourceBlock edge hIncident
  exact picture.only_surviving edge hBlock hLabel hSurvives

/-- A named surviving branch occurrence of the incoming datum. -/
noncomputable def branchEdge (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (label : Fin 4)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge label) sheet)) :
    NonDanglingEdge data :=
  ⟨data.sourceEdge (star.edge label) sheet, hSurvives⟩

@[simp] theorem branchEdge_val (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (label : Fin 4)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling data (data.sourceEdge (star.edge label) sheet)) :
    (branchEdge data star label sheet hSurvives).1 =
      data.sourceEdge (star.edge label) sheet := rfl

/-- The two canonical nd2 branch occurrences already lie on one old stable
row: the source picture connects them directly or through one internal
surviving occurrence. -/
theorem nd2_old_stablePath_eq {sourceBlock : WallBlock data wall}
    {block : Nd2Block}
    (picture : AuxR0Nd2Picture data star sourceBlock block) :
    (branchEdge data star block.first sourceBlock.1
        picture.first_survives).stablePath =
      (branchEdge data star block.second sourceBlock.1
        picture.second_survives).stablePath := by
  have hConnected := picture.connected
  cases hMiddle : picture.middle with
  | none =>
      rw [hMiddle] at hConnected
      exact stablePath_eq_of_consecutive hConnected
  | some middle =>
      rw [hMiddle] at hConnected
      exact (stablePath_eq_of_consecutive hConnected.1).trans
        (stablePath_eq_of_consecutive hConnected.2)

/-- Distinct star labels give distinct canonical occurrences. -/
theorem sourceEdge_ne_of_label_ne' (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) {first second : Fin 4}
    (hNe : first ≠ second) (firstSheet secondSheet : Fin degree) :
    data.sourceEdge (star.edge first) firstSheet ≠
      data.sourceEdge (star.edge second) secondSheet := by
  intro hEq
  exact hNe (star.edge_injective
    (congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hEq))

/-- The canonical branch occurrences of an nd2 block are distinct. -/
theorem nd2_branch_ne {sourceBlock : WallBlock data wall} {block : Nd2Block}
    (picture : AuxR0Nd2Picture data star sourceBlock block) :
    branchEdge data star block.first sourceBlock.1 picture.first_survives ≠
      branchEdge data star block.second sourceBlock.1 picture.second_survives :=
  fun hEq ↦ sourceEdge_ne_of_label_ne' data star block.distinct sourceBlock.1
    sourceBlock.1 (congrArg Subtype.val hEq)

/-- A canonical branch occurrence through a wall block meets that block's old
wall vertex. -/
theorem branch_incident_wallVertex (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (sourceBlock : WallBlock data wall) (label : Fin 4) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    Incident data (data.sourceEdge (star.edge label) sheet)
      (WallBlock.sourceVertex data wall sourceBlock) :=
  (incident_wallBlock_sourceVertex_iff data sourceBlock _).mpr
    ⟨star.edge_mem_incidentEdges label,
      WallBlock.ofSourceEdge_eq_of_rel data star sourceBlock label sheet hRel⟩

/-- **Dangling wall block.**  Its old wall vertex is isolated in the pruned
incoming source. -/
theorem dangling_old_nonDanglingValency (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (sourceBlock : WallBlock data wall)
    (old_dangling : ∀ (edge : data.SourceEdge) (label : Fin 4),
      WallBlock.ofSheet data wall edge.1.2 = sourceBlock →
      star.edge label = edge.1.1 → IsDangling data edge) :
    nonDanglingValency data
      (WallBlock.sourceVertex data wall sourceBlock) = 0 := by
  classical
  rw [← card_nonDanglingIncident, Finset.card_eq_zero,
    Finset.eq_empty_iff_forall_notMem]
  intro edge hEdge
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hEdge
  exact dangling_not_incident data star sourceBlock old_dangling edge hSurvives
    hIncident

/-- **nd2 wall block.**  Its old wall vertex is divalent: exactly the two
canonical branch occurrences survive there. -/
theorem nd2_old_nonDanglingValency {sourceBlock : WallBlock data wall}
    {block : Nd2Block}
    (picture : AuxR0Nd2Picture data star sourceBlock block) :
    nonDanglingValency data
      (WallBlock.sourceVertex data wall sourceBlock) = 2 := by
  classical
  rw [← card_nonDanglingIncident]
  have hSet : nonDanglingIncident data
        (WallBlock.sourceVertex data wall sourceBlock) =
      {data.sourceEdge (star.edge block.first) sourceBlock.1,
        data.sourceEdge (star.edge block.second) sourceBlock.1} := by
    ext edge
    rw [mem_nonDanglingIncident]
    constructor
    · rintro ⟨hSurvives, hIncident⟩
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        nd2_old_survivor_eq picture edge hSurvives hIncident
    · intro hMem
      rcases Finset.mem_insert.mp hMem with hEdge | hEdge
      · exact hEdge ▸ ⟨picture.first_survives, branch_incident_wallVertex data
          star sourceBlock block.first sourceBlock.1 rfl⟩
      · rw [Finset.mem_singleton] at hEdge
        exact hEdge ▸ ⟨picture.second_survives, branch_incident_wallVertex data
          star sourceBlock block.second sourceBlock.1 rfl⟩
  rw [hSet]
  exact Finset.card_pair
    (sourceEdge_ne_of_label_ne' data star block.distinct _ _)

/-- **nd3 wall block.**  Its old wall vertex is trivalent: exactly the three
canonical branch occurrences survive there. -/
theorem nd3_old_nonDanglingValency {sourceBlock : WallBlock data wall}
    {block : Nd3Block}
    (picture : AuxR0Nd3Picture data star sourceBlock block) :
    nonDanglingValency data
      (WallBlock.sourceVertex data wall sourceBlock) = 3 := by
  classical
  rw [← card_nonDanglingIncident]
  have hSet : nonDanglingIncident data
        (WallBlock.sourceVertex data wall sourceBlock) =
      block.activeLabels.image fun label ↦
        data.sourceEdge (star.edge label) (picture.activeSheet label) := by
    ext edge
    rw [mem_nonDanglingIncident]
    constructor
    · rintro ⟨hSurvives, hIncident⟩
      obtain ⟨hBlock, hLabel⟩ :=
        old_survivor_info data star sourceBlock edge hIncident
      obtain ⟨label, hActive, hEdge⟩ :=
        picture.only_surviving edge hBlock hLabel hSurvives
      exact Finset.mem_image.mpr ⟨label, hActive, hEdge.symm⟩
    · intro hMem
      obtain ⟨label, hActive, hEdge⟩ := Finset.mem_image.mp hMem
      exact hEdge ▸ ⟨picture.active_survives label hActive,
        branch_incident_wallVertex data star sourceBlock label _
          (picture.active_sheet label hActive)⟩
  have hInj : Set.InjOn
      (fun label ↦ data.sourceEdge (star.edge label) (picture.activeSheet label))
      ↑block.activeLabels := by
    intro first _ second _ hEq
    exact star.edge_injective
      (congrArg (fun e : data.SourceEdge ↦ e.1.1) hEq)
  rw [hSet, Finset.card_image_of_injOn hInj]
  simp [Nd3Block.activeLabels, block.first_ne_second, block.first_ne_third,
    block.second_ne_third]

/-- An nd3 wall vertex is never a stable-path junction. -/
theorem nd3_old_nonDanglingValency_ne_two {sourceBlock : WallBlock data wall}
    {block : Nd3Block}
    (picture : AuxR0Nd3Picture data star sourceBlock block) :
    nonDanglingValency data
      (WallBlock.sourceVertex data wall sourceBlock) ≠ 2 := by
  rw [nd3_old_nonDanglingValency picture]
  decide

end Old


/-! ## The actual outgoing candidates and their retained occurrences -/

section Candidate

variable {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall}
  [DecidableEq target.edges]

/-- The actual outgoing W4 candidate attached to one target pairing.  This is
the literal member of the semantic family, not a repackaging of the presented
path lists. -/
noncomputable def member (input : AuxR0SourceInput data star) (pairing : Fin 3) :
    BalancedGlobal.Candidate target degree data wall :=
  (input.presentedFamily data star).candidate pairing

theorem member_eq (input : AuxR0SourceInput data star) (pairing : Fin 3) :
    member input pairing = (input.presentedFamily data star).candidate pairing :=
  rfl

theorem member_sourceGenus (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    genus (member input pairing).datum.sourceGraph = genus data.sourceGraph :=
  candidate_sourceGenus input pairing

/-- The retained copy of a surviving incoming occurrence. -/
noncomputable def retained (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (edge : NonDanglingEdge data) :
    NonDanglingEdge (member input pairing).datum :=
  retainedEdge (member input pairing) input.valid.1 edge

@[simp] theorem retained_val (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (edge : NonDanglingEdge data) :
    (retained input pairing edge).1 =
      (member input pairing).oldSourceEdge edge.1 := rfl

theorem retained_injective (input : AuxR0SourceInput data star)
    (pairing : Fin 3) : Function.Injective (retained input pairing) :=
  retainedEdge_injective (member input pairing) input.valid.1

/-- The surviving regrown occurrence above a chosen sheet. -/
noncomputable def regrownEdge (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sheet)) :
    NonDanglingEdge (member input pairing).datum :=
  ⟨(member input pairing).newSourceEdge sheet, hSurvives⟩

@[simp] theorem regrownEdge_val (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sheet)) :
    (regrownEdge input pairing sheet hSurvives).1 =
      (member input pairing).newSourceEdge sheet := rfl

/-- The expanded endpoint of the outgoing candidate on one side, above a
chosen sheet. -/
noncomputable def sideEndpoint (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (side : Bool) (sheet : Fin degree) :
    (member input pairing).datum.SourceVertex :=
  (member input pairing).datum.sourceEndpoint (sideVertex target wall side) sheet

/-- Two surviving occurrences listed by the census at a divalent expanded
endpoint are consecutive there. -/
theorem consecutive_side (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (side : Bool) (sheet : Fin degree)
    (first second : NonDanglingEdge (member input pairing).datum)
    (hNe : first ≠ second)
    (hFirst : first.1 ∈ nonDanglingIncident (member input pairing).datum
      (sideEndpoint input pairing side sheet))
    (hSecond : second.1 ∈ nonDanglingIncident (member input pairing).datum
      (sideEndpoint input pairing side sheet))
    (hValency : nonDanglingValency (member input pairing).datum
      (sideEndpoint input pairing side sheet) = 2) :
    Consecutive (member input pairing).datum first second :=
  ⟨hNe, sideEndpoint input pairing side sheet,
    ((mem_nonDanglingIncident _ _ _).mp hFirst).2,
    ((mem_nonDanglingIncident _ _ _).mp hSecond).2, hValency⟩

/-! ### The two canonical nd2 survivors keep one outgoing stable row -/

/-- **Same-side nd2 block.**  The two canonical branch occurrences stay
directly consecutive at the endpoint that keeps the whole old block. -/
theorem nd2_same_retained_stablePath_eq (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    (retained input pairing (branchEdge data star block.first sourceBlock.1
        picture.first_survives)).stablePath =
      (retained input pairing (branchEdge data star block.second sourceBlock.1
        picture.second_survives)).stablePath := by
  have hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sourceBlock.1 :=
    rfl
  have hCensus := nd2_same_activeSide_census input pairing sourceBlock block
    picture hPicture hSame sourceBlock.1 hSheet
  apply stablePath_eq_of_consecutive
  refine consecutive_side input pairing
    (W4TargetPairings.Pairing.labelRight pairing block.first) sourceBlock.1 _ _
    (fun hEq ↦ nd2_branch_ne picture (retained_injective input pairing hEq))
    ((hCensus _).mpr (Or.inl rfl)) ((hCensus _).mpr (Or.inr rfl)) ?_
  exact nd2_same_activeSide_nonDanglingValency input pairing sourceBlock block
    picture hPicture hSame sourceBlock.1 hSheet

/-- **Opposite-side nd2 block.**  The two canonical branch occurrences are
joined through the single surviving regrown occurrence, one consecutive step
at each expanded endpoint. -/
theorem nd2_ne_retained_stablePath_eq (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    (retained input pairing (branchEdge data star block.first sourceBlock.1
        picture.first_survives)).stablePath =
      (retained input pairing (branchEdge data star block.second sourceBlock.1
        picture.second_survives)).stablePath := by
  have hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sourceBlock.1 :=
    rfl
  have hNewSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sourceBlock.1) :=
    nd2_new_survives_of_ne input pairing sourceBlock block picture hPicture hNe
  have hFirstCensus := nd2_ne_census input pairing sourceBlock block picture
    hPicture hNe block.first (Or.inl rfl) sourceBlock.1 hSheet
  have hSecondCensus := nd2_ne_census input pairing sourceBlock block picture
    hPicture hNe block.second (Or.inr rfl) sourceBlock.1 hSheet
  have hFirstStep : Consecutive (member input pairing).datum
      (retained input pairing (branchEdge data star block.first sourceBlock.1
        picture.first_survives))
      (regrownEdge input pairing sourceBlock.1 hNewSurvives) := by
    refine consecutive_side input pairing
      (W4TargetPairings.Pairing.labelRight pairing block.first) sourceBlock.1
      _ _ (fun hEq ↦ oldSourceEdge_ne_newSourceEdge (member input pairing) _ _
        (congrArg Subtype.val hEq))
      ((hFirstCensus _).mpr (Or.inl rfl)) ((hFirstCensus _).mpr (Or.inr rfl)) ?_
    exact nd2_ne_nonDanglingValency input pairing sourceBlock block picture
      hPicture hNe block.first (Or.inl rfl) sourceBlock.1 hSheet
  have hSecondStep : Consecutive (member input pairing).datum
      (retained input pairing (branchEdge data star block.second sourceBlock.1
        picture.second_survives))
      (regrownEdge input pairing sourceBlock.1 hNewSurvives) := by
    refine consecutive_side input pairing
      (W4TargetPairings.Pairing.labelRight pairing block.second) sourceBlock.1
      _ _ (fun hEq ↦ oldSourceEdge_ne_newSourceEdge (member input pairing) _ _
        (congrArg Subtype.val hEq))
      ((hSecondCensus _).mpr (Or.inl rfl))
      ((hSecondCensus _).mpr (Or.inr rfl)) ?_
    exact nd2_ne_nonDanglingValency input pairing sourceBlock block picture
      hPicture hNe block.second (Or.inr rfl) sourceBlock.1 hSheet
  exact (stablePath_eq_of_consecutive hFirstStep).trans
    (stablePath_eq_of_consecutive hSecondStep).symm

/-- Either way, the two canonical nd2 branch occurrences retain one outgoing
stable row. -/
theorem nd2_retained_stablePath_eq (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture) :
    (retained input pairing (branchEdge data star block.first sourceBlock.1
        picture.first_survives)).stablePath =
      (retained input pairing (branchEdge data star block.second sourceBlock.1
        picture.second_survives)).stablePath := by
  by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second
  · exact nd2_same_retained_stablePath_eq input pairing sourceBlock block
      picture hPicture hSame
  · exact nd2_ne_retained_stablePath_eq input pairing sourceBlock block picture
      hPicture hSame


/-! ### The occurrence-induced row map

Every old consecutive pair keeps one outgoing stable row.  At an nd2 wall
junction the two canonical survivors either stay directly consecutive or are
joined through the regrown occurrence; an nd3 wall vertex is trivalent and
carries no junction; a dangling wall vertex carries no survivor at all.
-/

/-- The defining relation of the incoming stable quotient is respected by
retention. -/
theorem retained_stablePath_eq_of_consecutive (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (first second : NonDanglingEdge data)
    (hConsecutive : Consecutive data first second) :
    (retained input pairing first).stablePath =
      (retained input pairing second).stablePath := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  by_cases hAt : vertex.1.1 = wall
  · obtain ⟨sourceBlock, hVertex⟩ :=
      exists_wallBlock_sourceVertex data wall vertex hAt
    subst hVertex
    cases hPicture : input.blockPicture sourceBlock with
    | dangling old_dangling =>
        exact (dangling_not_incident data star sourceBlock old_dangling first.1
          first.2 hFirst).elim
    | nd2 block picture =>
        have hRow := nd2_retained_stablePath_eq input pairing sourceBlock block
          picture hPicture
        rcases nd2_old_survivor_eq picture first.1 first.2 hFirst with
          hFirstVal | hFirstVal <;>
          rcases nd2_old_survivor_eq picture second.1 second.2 hSecond with
            hSecondVal | hSecondVal
        · exact (hNe (Subtype.ext (hFirstVal.trans hSecondVal.symm))).elim
        · rw [show first = branchEdge data star block.first sourceBlock.1
              picture.first_survives from Subtype.ext hFirstVal,
            show second = branchEdge data star block.second sourceBlock.1
              picture.second_survives from Subtype.ext hSecondVal]
          exact hRow
        · rw [show first = branchEdge data star block.second sourceBlock.1
              picture.second_survives from Subtype.ext hFirstVal,
            show second = branchEdge data star block.first sourceBlock.1
              picture.first_survives from Subtype.ext hSecondVal]
          exact hRow.symm
        · exact (hNe (Subtype.ext (hFirstVal.trans hSecondVal.symm))).elim
    | nd3 block picture =>
        exact (nd3_old_nonDanglingValency_ne_two picture hValency).elim
  · exact stablePath_eq_of_consecutive
      (consecutive_retained_of_away (member input pairing) input.valid
        (member_sourceGenus input pairing) first second hNe vertex hAt hFirst
        hSecond hValency)

/-- **The occurrence-induced stable-row map.**  It is induced by retaining an
actual surviving occurrence of the incoming datum, not read off a path list. -/
noncomputable def stablePathLift (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    StablePath data → StablePath (member input pairing).datum :=
  Quot.lift (fun edge ↦ (retained input pairing edge).stablePath)
    (fun _ _ hConsecutive ↦
      retained_stablePath_eq_of_consecutive input pairing _ _ hConsecutive)

@[simp] theorem stablePathLift_mk (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (edge : NonDanglingEdge data) :
    stablePathLift input pairing edge.stablePath =
      (retained input pairing edge).stablePath := rfl

/-! ### The old occurrence represented by a surviving regrown occurrence -/

/-- The canonical incoming occurrence attached to one source picture: the
first active branch of an nd2 block and the isolated branch of an nd3 block.
The dangling value is never reached, because no regrown occurrence survives
above a dangling block. -/
noncomputable def pictureOldSourceEdge (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall)
    (picture : AuxR0BlockPicture data star sourceBlock) : data.SourceEdge :=
  match picture with
  | .dangling _ => data.sourceEdge (star.edge 0) sourceBlock.1
  | .nd2 block _ => data.sourceEdge (star.edge block.first) sourceBlock.1
  | .nd3 block picture =>
      data.sourceEdge (star.edge (block.singletonLabel pairing))
        (picture.activeSheet (block.singletonLabel pairing))

/-- The canonical incoming occurrence attached to one old wall block. -/
noncomputable def blockOldSourceEdge (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) : data.SourceEdge :=
  pictureOldSourceEdge data star pairing sourceBlock
    (input.blockPicture sourceBlock)

omit [DecidableEq target.edges] in
theorem blockOldSourceEdge_nd2 (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture) :
    blockOldSourceEdge input pairing sourceBlock =
      data.sourceEdge (star.edge block.first) sourceBlock.1 := by
  rw [blockOldSourceEdge, hPicture]
  rfl

omit [DecidableEq target.edges] in
theorem blockOldSourceEdge_nd3 (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture) :
    blockOldSourceEdge input pairing sourceBlock =
      data.sourceEdge (star.edge (block.singletonLabel pairing))
        (picture.activeSheet (block.singletonLabel pairing)) := by
  rw [blockOldSourceEdge, hPicture]
  rfl

/-- The canonical incoming occurrence attached to the sheet of a regrown
occurrence, through the source picture of that sheet's old wall block. -/
noncomputable def newOldSourceEdge (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree) : data.SourceEdge :=
  blockOldSourceEdge input pairing (WallBlock.ofSheet data wall sheet)

omit [DecidableEq target.edges] in
theorem newOldSourceEdge_anchor (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) :
    newOldSourceEdge input pairing sourceBlock.1 =
      blockOldSourceEdge input pairing sourceBlock :=
  congrArg (blockOldSourceEdge input pairing)
    (WallBlock.ofSheet_anchor data wall sourceBlock)

omit [DecidableEq target.edges] in
theorem newOldSourceEdge_nd2 (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star (WallBlock.ofSheet data wall sheet)
      block)
    (hPicture : input.blockPicture (WallBlock.ofSheet data wall sheet) =
      .nd2 block picture) :
    newOldSourceEdge input pairing sheet =
      data.sourceEdge (star.edge block.first)
        (WallBlock.ofSheet data wall sheet).1 :=
  blockOldSourceEdge_nd2 input pairing _ block picture hPicture

omit [DecidableEq target.edges] in
theorem newOldSourceEdge_nd3 (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star (WallBlock.ofSheet data wall sheet)
      block)
    (hPicture : input.blockPicture (WallBlock.ofSheet data wall sheet) =
      .nd3 block picture) :
    newOldSourceEdge input pairing sheet =
      data.sourceEdge (star.edge (block.singletonLabel pairing))
        (picture.activeSheet (block.singletonLabel pairing)) :=
  blockOldSourceEdge_nd3 input pairing _ block picture hPicture

theorem newOldSourceEdge_survives (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sheet)) :
    ¬ IsDangling data (newOldSourceEdge input pairing sheet) := by
  cases hPicture : input.blockPicture (WallBlock.ofSheet data wall sheet) with
  | dangling old_dangling =>
      exact absurd (dangling_new_dangles input pairing _ old_dangling hPicture
        sheet (rel_ofSheet data wall sheet)) hSurvives
  | nd2 block picture =>
      rw [newOldSourceEdge_nd2 input pairing sheet block picture hPicture]
      exact picture.first_survives
  | nd3 block picture =>
      rw [newOldSourceEdge_nd3 input pairing sheet block picture hPicture]
      exact picture.active_survives _ (block.singletonLabel_mem_activeLabels _)

/-- The surviving incoming occurrence represented by a surviving regrown
occurrence. -/
noncomputable def newOldEdge (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sheet)) : NonDanglingEdge data :=
  ⟨newOldSourceEdge input pairing sheet,
    newOldSourceEdge_survives input pairing sheet hSurvives⟩

/-- **Every surviving regrown occurrence shares an outgoing stable row with a
retained one.**  On an opposite-side nd2 block it is consecutive with the
first active branch's survivor; on an nd3 block with the isolated branch's
survivor. -/
theorem regrown_stablePath_eq (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sheet)) :
    (retained input pairing
        (newOldEdge input pairing sheet hSurvives)).stablePath =
      (regrownEdge input pairing sheet hSurvives).stablePath := by
  have hSheet := rel_ofSheet data wall sheet
  cases hPicture : input.blockPicture (WallBlock.ofSheet data wall sheet) with
  | dangling old_dangling =>
      exact absurd (dangling_new_dangles input pairing _ old_dangling hPicture
        sheet hSheet) hSurvives
  | nd2 block picture =>
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · exact absurd (nd2_new_dangles_of_same input pairing _ block picture
          hPicture hSame sheet hSheet) hSurvives
      · have hEdge : newOldEdge input pairing sheet hSurvives =
            branchEdge data star block.first
              (WallBlock.ofSheet data wall sheet).1 picture.first_survives :=
          Subtype.ext (newOldSourceEdge_nd2 input pairing sheet block picture
            hPicture)
        rw [hEdge]
        apply stablePath_eq_of_consecutive
        have hCensus := nd2_ne_census input pairing _ block picture hPicture
          hSame block.first (Or.inl rfl) sheet hSheet
        refine consecutive_side input pairing
          (W4TargetPairings.Pairing.labelRight pairing block.first) sheet _ _
          (fun hEq ↦ oldSourceEdge_ne_newSourceEdge (member input pairing) _ _
            (congrArg Subtype.val hEq))
          ((hCensus _).mpr (Or.inl rfl))
          ((mem_nonDanglingIncident _ _ _).mpr
            ⟨hSurvives, new_incident_side (inputReceipts input pairing) _ sheet⟩)
          ?_
        exact nd2_ne_nonDanglingValency input pairing _ block picture hPicture
          hSame block.first (Or.inl rfl) sheet hSheet
  | nd3 block picture =>
      have hRel := (nd3_new_survives_iff input pairing _ block picture hPicture
        sheet hSheet).mp hSurvives
      have hEdge : newOldEdge input pairing sheet hSurvives =
          branchEdge data star (block.singletonLabel pairing)
            (picture.activeSheet (block.singletonLabel pairing))
            (picture.active_survives _
              (block.singletonLabel_mem_activeLabels pairing)) :=
        Subtype.ext (newOldSourceEdge_nd3 input pairing sheet block picture
          hPicture)
      rw [hEdge]
      apply stablePath_eq_of_consecutive
      have hCensus := nd3_singletonSide_census input pairing _ block picture
        hPicture sheet hRel
      refine consecutive_side input pairing
        (W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing)) sheet _ _
        (fun hEq ↦ oldSourceEdge_ne_newSourceEdge (member input pairing) _ _
          (congrArg Subtype.val hEq))
        ((hCensus _).mpr (Or.inl rfl))
        ((mem_nonDanglingIncident _ _ _).mpr
          ⟨hSurvives, new_incident_side (inputReceipts input pairing) _ sheet⟩)
        ?_
      exact nd3_singletonSide_nonDanglingValency input pairing _ block picture
        hPicture sheet hRel


/-! ### Surjectivity of the induced row map -/

/-- Every surviving occurrence of an outgoing candidate lies on the outgoing
row of an actual retained incoming survivor. -/
theorem exists_retained_row (input : AuxR0SourceInput data star)
    (pairing : Fin 3)
    (edge : NonDanglingEdge (member input pairing).datum) :
    ∃ old : NonDanglingEdge data,
      (retained input pairing old).stablePath = edge.stablePath := by
  rcases nonDanglingEdge_cases (member input pairing) input.valid
      (member_sourceGenus input pairing) edge with
    ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · exact ⟨old, rfl⟩
  · exact ⟨newOldEdge input pairing sheet hSurvives,
      regrown_stablePath_eq input pairing sheet hSurvives⟩

theorem stablePathLift_surjective (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    Function.Surjective (stablePathLift input pairing) := by
  intro path
  induction path using Quot.inductionOn with
  | h edge =>
      obtain ⟨old, hPath⟩ := exists_retained_row input pairing edge
      exact ⟨old.stablePath, hPath⟩

/-! ### The geometric left inverse -/

/-- A surviving occurrence that is not retained is an actual surviving regrown
occurrence. -/
theorem new_representation (input : AuxR0SourceInput data star)
    (pairing : Fin 3)
    (edge : NonDanglingEdge (member input pairing).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retained input pairing old = edge) :
    ∃ (sheet : Fin degree) (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sheet)),
      edge = regrownEdge input pairing sheet hSurvives := by
  rcases nonDanglingEdge_cases (member input pairing) input.valid
      (member_sourceGenus input pairing) edge with
    ⟨old, hOld⟩ | ⟨sheet, hSurvives, hNew⟩
  · exact (hNotOld ⟨old, hOld.symm⟩).elim
  · exact ⟨sheet, hSurvives, hNew⟩

noncomputable def newSheet (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (edge : NonDanglingEdge (member input pairing).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retained input pairing old = edge) : Fin degree :=
  (new_representation input pairing edge hNotOld).choose

theorem newSheet_survives (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (edge : NonDanglingEdge (member input pairing).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retained input pairing old = edge) :
    ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge
        (newSheet input pairing edge hNotOld)) :=
  (new_representation input pairing edge hNotOld).choose_spec.choose

theorem newSheet_spec (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (edge : NonDanglingEdge (member input pairing).datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retained input pairing old = edge) :
    edge = regrownEdge input pairing (newSheet input pairing edge hNotOld)
      (newSheet_survives input pairing edge hNotOld) :=
  (new_representation input pairing edge hNotOld).choose_spec.choose_spec

/-- Two regrown occurrences that agree have the same old wall block, hence the
same canonical incoming occurrence. -/
theorem newOldSourceEdge_congr (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (first second : Fin degree)
    (hEq : (member input pairing).newSourceEdge first =
      (member input pairing).newSourceEdge second) :
    newOldSourceEdge input pairing first =
      newOldSourceEdge input pairing second := by
  have hRel :=
    (newSourceEdge_eq_iff (inputReceipts input pairing) first second).mp hEq
  have hWall := (newEdge_refines_wall data star
    input.activeProfile.blockPattern pairing).rel hRel
  exact congrArg (blockOldSourceEdge input pairing) (Subtype.ext hWall)

/-- Retained occurrences return to their own incoming row; a surviving regrown
occurrence returns to the row of the canonical incoming occurrence of its old
wall block. -/
noncomputable def rowOfEdge (input : AuxR0SourceInput data star)
    (pairing : Fin 3)
    (edge : NonDanglingEdge (member input pairing).datum) : StablePath data := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge data,
      retained input pairing old = edge then
    (Classical.choose hOld).stablePath
  else
    (newOldEdge input pairing (newSheet input pairing edge hOld)
      (newSheet_survives input pairing edge hOld)).stablePath

@[simp] theorem rowOfEdge_retained (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (old : NonDanglingEdge data) :
    rowOfEdge input pairing (retained input pairing old) = old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge data,
      retained input pairing other = retained input pairing old := ⟨old, rfl⟩
  rw [rowOfEdge, dite_eq_left hOld]
  exact congrArg NonDanglingEdge.stablePath
    (retained_injective input pairing (Classical.choose_spec hOld))

theorem regrownEdge_not_retained (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sheet)) :
    ¬ ∃ old : NonDanglingEdge data,
      retained input pairing old = regrownEdge input pairing sheet hSurvives := by
  rintro ⟨old, hOld⟩
  exact oldSourceEdge_ne_newSourceEdge (member input pairing) old.1 sheet
    (congrArg Subtype.val hOld)

theorem rowOfEdge_new (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sheet)) :
    rowOfEdge input pairing (regrownEdge input pairing sheet hSurvives) =
      (newOldEdge input pairing sheet hSurvives).stablePath := by
  classical
  have hNotOld := regrownEdge_not_retained input pairing sheet hSurvives
  rw [rowOfEdge, dite_eq_right hNotOld]
  refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
  refine newOldSourceEdge_congr input pairing _ sheet ?_
  exact (congrArg Subtype.val
    (newSheet_spec input pairing _ hNotOld)).symm

/-- The reverse assignment of a surviving regrown occurrence is the outgoing
row it actually lies on. -/
theorem rowOfEdge_regrown_stablePath (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sheet)) :
    stablePathLift input pairing
        (rowOfEdge input pairing (regrownEdge input pairing sheet hSurvives)) =
      (regrownEdge input pairing sheet hSurvives).stablePath := by
  rw [rowOfEdge_new]
  exact regrown_stablePath_eq input pairing sheet hSurvives


/-- Exhaustion of the surviving occurrences of an outgoing candidate, in the
named form used below. -/
theorem nonDanglingEdge_cases' (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (edge : NonDanglingEdge (member input pairing).datum) :
    (∃ old : NonDanglingEdge data, edge = retained input pairing old) ∨
      ∃ (sheet : Fin degree) (hSurvives : ¬ IsDangling (member input pairing).datum
        ((member input pairing).newSourceEdge sheet)),
        edge = regrownEdge input pairing sheet hSurvives :=
  nonDanglingEdge_cases (member input pairing) input.valid
    (member_sourceGenus input pairing) edge

/-- Away from the expanded wall both survivors at a divalent vertex are
retained, and their incoming rows meet there. -/
theorem rowOfEdge_eq_away (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge (member input pairing).datum)
    (hFirst : Incident (member input pairing).datum first.1
      (retainedVertex (member input pairing) vertex))
    (hSecond : Incident (member input pairing).datum second.1
      (retainedVertex (member input pairing) vertex))
    (hValency : nonDanglingValency (member input pairing).datum
      (retainedVertex (member input pairing) vertex) = 2) :
    rowOfEdge input pairing first = rowOfEdge input pairing second := by
  classical
  rcases nonDanglingEdge_cases' input pairing first with
    ⟨oldFirst, rfl⟩ | ⟨sheetFirst, hFirstSurvives, rfl⟩
  · rcases nonDanglingEdge_cases' input pairing second with
      ⟨oldSecond, rfl⟩ | ⟨sheetSecond, hSecondSurvives, rfl⟩
    · rw [rowOfEdge_retained, rowOfEdge_retained]
      by_cases hEqual : oldFirst = oldSecond
      · exact congrArg NonDanglingEdge.stablePath hEqual
      · exact stablePath_eq_of_consecutive ⟨hEqual, vertex,
          (incident_oldSourceEdge_iff (member input pairing) vertex hAway
            oldFirst.1).mp hFirst,
          (incident_oldSourceEdge_iff (member input pairing) vertex hAway
            oldSecond.1).mp hSecond,
          (nonDanglingValency_retainedVertex (member input pairing) input.valid
            (member_sourceGenus input pairing) vertex hAway).symm.trans
            hValency⟩
    · exact (not_incident_newSourceEdge (member input pairing) vertex hAway
        sheetSecond hSecond).elim
  · exact (not_incident_newSourceEdge (member input pairing) vertex hAway
      sheetFirst hFirst).elim

/-! ### The reverse assignment at the two expanded endpoints -/

/-- **Same-side nd2 block.**  Both survivors at the joined endpoint are
canonical branch occurrences of one incoming row. -/
theorem rowOfEdge_nd2_same (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (edge : NonDanglingEdge (member input pairing).datum)
    (hIncident : Incident (member input pairing).datum edge.1
      (sideEndpoint input pairing
        (W4TargetPairings.Pairing.labelRight pairing block.first) sheet)) :
    rowOfEdge input pairing edge =
      (branchEdge data star block.first sourceBlock.1
        picture.first_survives).stablePath := by
  have hCensus := nd2_same_activeSide_census input pairing sourceBlock block
    picture hPicture hSame sheet hSheet
  rcases (hCensus edge.1).mp
      ((mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩) with
    hValue | hValue
  · rw [show edge = retained input pairing (branchEdge data star block.first
        sourceBlock.1 picture.first_survives) from Subtype.ext hValue,
      rowOfEdge_retained]
  · rw [show edge = retained input pairing (branchEdge data star block.second
        sourceBlock.1 picture.second_survives) from Subtype.ext hValue,
      rowOfEdge_retained]
    exact (nd2_old_stablePath_eq picture).symm

/-- The regrown occurrence above the anchor sheet of an nd2 block returns to
that block's first canonical branch occurrence. -/
theorem rowOfEdge_regrown_nd2 (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (edge : NonDanglingEdge (member input pairing).datum)
    (hValue : edge.1 = (member input pairing).newSourceEdge sourceBlock.1) :
    rowOfEdge input pairing edge =
      (branchEdge data star block.first sourceBlock.1
        picture.first_survives).stablePath := by
  have hSurvives : ¬ IsDangling (member input pairing).datum
      ((member input pairing).newSourceEdge sourceBlock.1) := by
    rw [← hValue]; exact edge.2
  rw [show edge = regrownEdge input pairing sourceBlock.1 hSurvives from
      Subtype.ext hValue, rowOfEdge_new]
  refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
  exact (newOldSourceEdge_anchor input pairing sourceBlock).trans
    (blockOldSourceEdge_nd2 input pairing sourceBlock block picture hPicture)

/-- **Opposite-side nd2 block.**  At either expanded endpoint every survivor
returns to the block's single incoming row. -/
theorem rowOfEdge_nd2_ne (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (picture : AuxR0Nd2Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd2 block picture)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (label : Fin 4) (hLabel : label = block.first ∨ label = block.second)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet)
    (edge : NonDanglingEdge (member input pairing).datum)
    (hIncident : Incident (member input pairing).datum edge.1
      (sideEndpoint input pairing
        (W4TargetPairings.Pairing.labelRight pairing label) sheet)) :
    rowOfEdge input pairing edge =
      (branchEdge data star block.first sourceBlock.1
        picture.first_survives).stablePath := by
  have hCensus := nd2_ne_census input pairing sourceBlock block picture hPicture
    hNe label hLabel sheet hSheet
  rcases (hCensus edge.1).mp
      ((mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩) with
    hValue | hValue
  · rcases hLabel with rfl | rfl
    · rw [show edge = retained input pairing (branchEdge data star block.first
          sourceBlock.1 picture.first_survives) from Subtype.ext hValue,
        rowOfEdge_retained]
    · rw [show edge = retained input pairing (branchEdge data star block.second
          sourceBlock.1 picture.second_survives) from Subtype.ext hValue,
        rowOfEdge_retained]
      exact (nd2_old_stablePath_eq picture).symm
  · exact rowOfEdge_regrown_nd2 input pairing sourceBlock block picture hPicture
      edge hValue

/-- **nd3 block, isolated endpoint.**  Every survivor there returns to the
isolated branch's own incoming row. -/
theorem rowOfEdge_nd3_singleton (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hRel : (data.edgePartition
        (star.edge (block.singletonLabel pairing))).Rel sheet
      (picture.activeSheet (block.singletonLabel pairing)))
    (edge : NonDanglingEdge (member input pairing).datum)
    (hIncident : Incident (member input pairing).datum edge.1
      (sideEndpoint input pairing
        (W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing)) sheet)) :
    rowOfEdge input pairing edge =
      (branchEdge data star (block.singletonLabel pairing)
        (picture.activeSheet (block.singletonLabel pairing))
        (picture.active_survives _
          (block.singletonLabel_mem_activeLabels pairing))).stablePath := by
  have hWallSheet : (data.vertexPartition wall).Rel sourceBlock.1 sheet :=
    (picture.active_sheet _ (block.singletonLabel_mem_activeLabels pairing)).trans
      ((star.edgePartition_refines_wall data
        (block.singletonLabel pairing)).rel hRel).symm
  have hCensus := nd3_singletonSide_census input pairing sourceBlock block
    picture hPicture sheet hRel
  rcases (hCensus edge.1).mp
      ((mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩) with
    hValue | hValue
  · rw [show edge = retained input pairing (branchEdge data star
        (block.singletonLabel pairing)
        (picture.activeSheet (block.singletonLabel pairing))
        (picture.active_survives _
          (block.singletonLabel_mem_activeLabels pairing))) from
      Subtype.ext hValue, rowOfEdge_retained]
  · have hSurvives : ¬ IsDangling (member input pairing).datum
        ((member input pairing).newSourceEdge sheet) :=
      fun hDangling ↦ edge.2 (by rw [hValue]; exact hDangling)
    rw [show edge = regrownEdge input pairing sheet hSurvives from
        Subtype.ext hValue, rowOfEdge_new]
    refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
    refine Eq.trans (congrArg (blockOldSourceEdge input pairing)
      (WallBlock.ofSheet_eq_of_rel data wall sourceBlock sheet hWallSheet)) ?_
    exact blockOldSourceEdge_nd3 input pairing sourceBlock block picture hPicture


/-- **The reverse assignment is constant at every divalent expanded
endpoint.**  The four source pictures are read against the proved endpoint
census: a dangling block and the split endpoints are isolated, the trivalent
nd3 endpoint is not a junction, and the remaining endpoints carry exactly one
incoming row. -/
theorem rowOfEdge_eq_side (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (side : Bool) (sheet : Fin degree)
    (hValency : nonDanglingValency (member input pairing).datum
      (sideEndpoint input pairing side sheet) = 2)
    (first second : NonDanglingEdge (member input pairing).datum)
    (hFirst : Incident (member input pairing).datum first.1
      (sideEndpoint input pairing side sheet))
    (hSecond : Incident (member input pairing).datum second.1
      (sideEndpoint input pairing side sheet)) :
    rowOfEdge input pairing first = rowOfEdge input pairing second := by
  have hSheet := rel_ofSheet data wall sheet
  cases hPicture : input.blockPicture (WallBlock.ofSheet data wall sheet) with
  | dangling old_dangling =>
      have hZero := dangling_nonDanglingValency_eq_zero input pairing _
        old_dangling hPicture side sheet hSheet
      exact absurd (hZero.symm.trans hValency) (by decide)
  | nd2 block picture =>
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · by_cases hSide :
            side = W4TargetPairings.Pairing.labelRight pairing block.first
        · subst hSide
          exact (rowOfEdge_nd2_same input pairing _ block picture hPicture hSame
              sheet hSheet first hFirst).trans
            (rowOfEdge_nd2_same input pairing _ block picture hPicture hSame
              sheet hSheet second hSecond).symm
        · have hSideEq :
              side = ! W4TargetPairings.Pairing.labelRight pairing block.first :=
            bool_eq_not_of_ne hSide
          subst hSideEq
          have hZero := nd2_same_otherSide_nonDanglingValency_eq_zero input
            pairing _ block picture hPicture hSame sheet hSheet
          exact absurd (hZero.symm.trans hValency) (by decide)
      · by_cases hSide :
            side = W4TargetPairings.Pairing.labelRight pairing block.first
        · subst hSide
          exact (rowOfEdge_nd2_ne input pairing _ block picture hPicture hSame
              block.first (Or.inl rfl) sheet hSheet first hFirst).trans
            (rowOfEdge_nd2_ne input pairing _ block picture hPicture hSame
              block.first (Or.inl rfl) sheet hSheet second hSecond).symm
        · have hSideEq :
              side = W4TargetPairings.Pairing.labelRight pairing block.second :=
            (bool_eq_not_of_ne hSide).trans
              (bool_eq_not_of_ne (Ne.symm hSame)).symm
          subst hSideEq
          exact (rowOfEdge_nd2_ne input pairing _ block picture hPicture hSame
              block.second (Or.inr rfl) sheet hSheet first hFirst).trans
            (rowOfEdge_nd2_ne input pairing _ block picture hPicture hSame
              block.second (Or.inr rfl) sheet hSheet second hSecond).symm
  | nd3 block picture =>
      by_cases hSide : side = W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing)
      · subst hSide
        by_cases hRel : (data.edgePartition
            (star.edge (block.singletonLabel pairing))).Rel sheet
          (picture.activeSheet (block.singletonLabel pairing))
        · exact (rowOfEdge_nd3_singleton input pairing _ block picture hPicture
              sheet hRel first hFirst).trans
            (rowOfEdge_nd3_singleton input pairing _ block picture hPicture
              sheet hRel second hSecond).symm
        · have hZero := nd3_singletonSide_residual_nonDanglingValency_eq_zero
            input pairing _ block picture hPicture sheet hSheet hRel
          exact absurd (hZero.symm.trans hValency) (by decide)
      · have hSideEq : side = ! W4TargetPairings.Pairing.labelRight pairing
            (block.singletonLabel pairing) := bool_eq_not_of_ne hSide
        subst hSideEq
        have hThree := nd3_otherSide_nonDanglingValency input pairing _ block
          picture hPicture sheet hSheet
        exact absurd (hThree.symm.trans hValency) (by decide)

/-- The reverse assignment is constant on every actual consecutive pair of the
outgoing candidate. -/
theorem rowOfEdge_eq_of_consecutive (input : AuxR0SourceInput data star)
    (pairing : Fin 3)
    (first second : NonDanglingEdge (member input pairing).datum)
    (hConsecutive : Consecutive (member input pairing).datum first second) :
    rowOfEdge input pairing first = rowOfEdge input pairing second := by
  obtain ⟨_, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  have hSelf : (member input pairing).datum.sourceEndpoint vertex.1.1
      vertex.1.2 = vertex :=
    ((member input pairing).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : vertex.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : sideEndpoint input pairing false vertex.1.2 = vertex :=
          (congrArg (fun place ↦ (member input pairing).datum.sourceEndpoint
            place vertex.1.2) hTarget.symm).trans hSelf
        rw [← hEndpoint] at hFirst hSecond hValency
        exact rowOfEdge_eq_side input pairing false vertex.1.2 hValency first
          second hFirst hSecond
      · obtain ⟨old, hOld, hVertex⟩ := exists_retainedVertex_of_target
          (member input pairing) vertex place hAt hTarget
        rw [← hVertex] at hFirst hSecond hValency
        exact rowOfEdge_eq_away input pairing old (hOld ▸ hAt) first second
          hFirst hSecond hValency
  | inr point =>
      cases point
      have hEndpoint : sideEndpoint input pairing true vertex.1.2 = vertex :=
        (congrArg (fun place ↦ (member input pairing).datum.sourceEndpoint
          place vertex.1.2) hTarget.symm).trans hSelf
      rw [← hEndpoint] at hFirst hSecond hValency
      exact rowOfEdge_eq_side input pairing true vertex.1.2 hValency first
        second hFirst hSecond

/-! ## The occurrence-induced stable-row equivalence -/

/-- The reverse row assignment descends through the outgoing stable
quotient. -/
noncomputable def stablePathDescend (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    StablePath (member input pairing).datum → StablePath data :=
  Quot.lift (rowOfEdge input pairing) (rowOfEdge_eq_of_consecutive input pairing)

@[simp] theorem stablePathDescend_mk (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (edge : NonDanglingEdge (member input pairing).datum) :
    stablePathDescend input pairing edge.stablePath =
      rowOfEdge input pairing edge := rfl

/-- Descent is a literal left inverse of the retained-occurrence lift. -/
theorem stablePathDescend_lift (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (path : StablePath data) :
    stablePathDescend input pairing (stablePathLift input pairing path) =
      path := by
  induction path using Quot.inductionOn with
  | h edge => exact rowOfEdge_retained input pairing edge

theorem stablePathLift_injective (input : AuxR0SourceInput data star)
    (pairing : Fin 3) : Function.Injective (stablePathLift input pairing) :=
  Function.LeftInverse.injective (stablePathDescend_lift input pairing)

/-- **The occurrence-induced stable-row equivalence of an outgoing W4
candidate.**  It is the retained-occurrence map of the incoming stable source,
with a geometric left inverse, and carries no extra hypothesis beyond the
source input itself. -/
noncomputable def stablePathEquiv (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    StablePath data ≃ StablePath (member input pairing).datum :=
  Equiv.ofBijective (stablePathLift input pairing)
    ⟨stablePathLift_injective input pairing,
      stablePathLift_surjective input pairing⟩

@[simp] theorem stablePathEquiv_mk (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (edge : NonDanglingEdge data) :
    stablePathEquiv input pairing edge.stablePath =
      (retained input pairing edge).stablePath := rfl

/-- The inverse of the row equivalence is the explicit reverse assignment. -/
@[simp] theorem stablePathEquiv_symm_apply (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (path : StablePath (member input pairing).datum) :
    (stablePathEquiv input pairing).symm path =
      stablePathDescend input pairing path := by
  obtain ⟨row, hRow⟩ := stablePathLift_surjective input pairing path
  rw [← hRow, stablePathDescend_lift]
  exact (stablePathEquiv input pairing).symm_apply_apply row


/-! ## Branch vertices of an outgoing candidate

The census of `W4OutgoingSurvival` is read here as a complete valency table at
the two expanded endpoints: a dangling block and the two split endpoints are
isolated, an nd2 block contributes only divalent endpoints, and the single
trivalent endpoint of an nd3 block is the only new branch vertex above the
wall.
-/

theorem member_vertexPartition_side (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (side : Bool) :
    (member input pairing).datum.vertexPartition (sideVertex target wall side) =
      sidePartition (wholeResolution data star input.activeProfile.blockPattern
        pairing) side :=
  datum_vertexPartition_sideVertex (inputReceipts input pairing) side

theorem sideEndpoint_target (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (side : Bool) (sheet : Fin degree) :
    (sideEndpoint input pairing side sheet).1.1 = sideVertex target wall side :=
  rfl

theorem sideEndpoint_eq_iff (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (side : Bool) (first second : Fin degree) :
    sideEndpoint input pairing side first =
        sideEndpoint input pairing side second ↔
      (sidePartition (wholeResolution data star input.activeProfile.blockPattern
        pairing) side).Rel first second := by
  have hPart := member_vertexPartition_side input pairing side
  constructor
  · intro hEq
    have hSheet : ((member input pairing).datum.vertexPartition
          (sideVertex target wall side)).repr first =
        ((member input pairing).datum.vertexPartition
          (sideVertex target wall side)).repr second :=
      congrArg (fun vertex : (member input pairing).datum.SourceVertex ↦
        vertex.1.2) hEq
    rw [hPart] at hSheet
    exact hSheet
  · intro hRel
    refine Subtype.ext (Prod.ext rfl ?_)
    show ((member input pairing).datum.vertexPartition
      (sideVertex target wall side)).repr first =
      ((member input pairing).datum.vertexPartition
        (sideVertex target wall side)).repr second
    rw [hPart]
    exact hRel

omit [DecidableEq target.edges] in
/-- Above an nd3 wall block the trivalent endpoint still carries the whole old
wall block. -/
theorem nd3_otherSide_rel (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel sourceBlock.1 sheet) :
    (sidePartition (wholeResolution data star input.activeProfile.blockPattern
        pairing)
      (! W4TargetPairings.Pairing.labelRight pairing
        (block.singletonLabel pairing))).Rel sourceBlock.1 sheet := by
  have hPattern : input.activeProfile.blockPattern sourceBlock.1 = .nd3 block :=
    blockPattern_eq_nd3_of_picture input sourceBlock block picture hPicture
  rw [wholeResolution_side_rel, sourceBlock.2,
    nd3_otherSide_partition data star input.activeProfile.blockPattern pairing
      sourceBlock.1 block hPattern]
  exact hRel

/-- **The only new branch vertex above a wall block is the trivalent nd3
endpoint.** -/
theorem branch_sideEndpoint (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (side : Bool) (sheet : Fin degree)
    (hBranch : 3 ≤ nonDanglingValency (member input pairing).datum
      (sideEndpoint input pairing side sheet)) :
    ∃ (block : Nd3Block) (picture : AuxR0Nd3Picture data star
        (WallBlock.ofSheet data wall sheet) block),
      input.blockPicture (WallBlock.ofSheet data wall sheet) =
          .nd3 block picture ∧
        side = ! W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing) := by
  have hSheet := rel_ofSheet data wall sheet
  cases hPicture : input.blockPicture (WallBlock.ofSheet data wall sheet) with
  | dangling old_dangling =>
      have hVal : nonDanglingValency (member input pairing).datum
          (sideEndpoint input pairing side sheet) = 0 :=
        dangling_nonDanglingValency_eq_zero input pairing _ old_dangling
          hPicture side sheet hSheet
      exact absurd hBranch (by omega)
  | nd2 block picture =>
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · by_cases hSide :
            side = W4TargetPairings.Pairing.labelRight pairing block.first
        · have hVal : nonDanglingValency (member input pairing).datum
              (sideEndpoint input pairing
                (W4TargetPairings.Pairing.labelRight pairing block.first)
                sheet) = 2 :=
            nd2_same_activeSide_nonDanglingValency input pairing _ block picture
              hPicture hSame sheet hSheet
          rw [hSide] at hBranch
          exact absurd hBranch (by omega)
        · have hVal : nonDanglingValency (member input pairing).datum
              (sideEndpoint input pairing
                (! W4TargetPairings.Pairing.labelRight pairing block.first)
                sheet) = 0 :=
            nd2_same_otherSide_nonDanglingValency_eq_zero input pairing _ block
              picture hPicture hSame sheet hSheet
          rw [bool_eq_not_of_ne hSide] at hBranch
          exact absurd hBranch (by omega)
      · by_cases hSide :
            side = W4TargetPairings.Pairing.labelRight pairing block.first
        · have hVal : nonDanglingValency (member input pairing).datum
              (sideEndpoint input pairing
                (W4TargetPairings.Pairing.labelRight pairing block.first)
                sheet) = 2 :=
            nd2_ne_nonDanglingValency input pairing _ block picture hPicture
              hSame block.first (Or.inl rfl) sheet hSheet
          rw [hSide] at hBranch
          exact absurd hBranch (by omega)
        · have hVal : nonDanglingValency (member input pairing).datum
              (sideEndpoint input pairing
                (W4TargetPairings.Pairing.labelRight pairing block.second)
                sheet) = 2 :=
            nd2_ne_nonDanglingValency input pairing _ block picture hPicture
              hSame block.second (Or.inr rfl) sheet hSheet
          rw [(bool_eq_not_of_ne hSide).trans
            (bool_eq_not_of_ne (Ne.symm hSame)).symm] at hBranch
          exact absurd hBranch (by omega)
  | nd3 block picture =>
      by_cases hSide : side = W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing)
      · by_cases hRel : (data.edgePartition
            (star.edge (block.singletonLabel pairing))).Rel sheet
          (picture.activeSheet (block.singletonLabel pairing))
        · have hVal : nonDanglingValency (member input pairing).datum
              (sideEndpoint input pairing
                (W4TargetPairings.Pairing.labelRight pairing
                  (block.singletonLabel pairing)) sheet) = 2 :=
            nd3_singletonSide_nonDanglingValency input pairing _ block picture
              hPicture sheet hRel
          rw [hSide] at hBranch
          exact absurd hBranch (by omega)
        · have hVal : nonDanglingValency (member input pairing).datum
              (sideEndpoint input pairing
                (W4TargetPairings.Pairing.labelRight pairing
                  (block.singletonLabel pairing)) sheet) = 0 :=
            nd3_singletonSide_residual_nonDanglingValency_eq_zero input pairing _
              block picture hPicture sheet hSheet hRel
          rw [hSide] at hBranch
          exact absurd hBranch (by omega)
      · exact ⟨block, picture, rfl, bool_eq_not_of_ne hSide⟩

/-- The side of an outgoing candidate carrying the trivalent endpoint of a wall
block, when that block has one. -/
noncomputable def branchSide (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) : Bool :=
  match input.blockPicture sourceBlock with
  | .dangling _ => false
  | .nd2 _ _ => false
  | .nd3 block _ =>
      ! W4TargetPairings.Pairing.labelRight pairing (block.singletonLabel pairing)

omit [DecidableEq target.edges] in
theorem branchSide_nd3 (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture) :
    branchSide input pairing sourceBlock =
      ! W4TargetPairings.Pairing.labelRight pairing
        (block.singletonLabel pairing) := by
  rw [branchSide, hPicture]

omit [DecidableEq target.edges] in
theorem sourceVertex_sheet (data : GluingDatum target degree) (wall : target.V)
    (sourceBlock : WallBlock data wall) :
    (WallBlock.sourceVertex data wall sourceBlock).1.2 = sourceBlock.1 :=
  sourceBlock.2

/-- The branch-vertex map of an outgoing candidate: retain every vertex away
from the wall, and send an nd3 wall vertex to its trivalent endpoint. -/
noncomputable def branchImage (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (vertex : data.SourceVertex) :
    (member input pairing).datum.SourceVertex :=
  if vertex.1.1 = wall then
    sideEndpoint input pairing
      (branchSide input pairing (WallBlock.ofSheet data wall vertex.1.2))
      vertex.1.2
  else retainedVertex (member input pairing) vertex

theorem branchImage_away (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall) :
    branchImage input pairing vertex = retainedVertex (member input pairing)
      vertex := by
  rw [branchImage, ite_eq_right hAway]

theorem branchImage_wall (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (sourceBlock : WallBlock data wall) :
    branchImage input pairing (WallBlock.sourceVertex data wall sourceBlock) =
      sideEndpoint input pairing (branchSide input pairing sourceBlock)
        sourceBlock.1 := by
  have hAt : (WallBlock.sourceVertex data wall sourceBlock).1.1 = wall := rfl
  rw [branchImage, ite_eq_left hAt, sourceVertex_sheet, WallBlock.ofSheet_anchor]

theorem three_le_branchImage (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (vertex : data.SourceVertex)
    (hBranch : 3 ≤ nonDanglingValency data vertex) :
    3 ≤ nonDanglingValency (member input pairing).datum
      (branchImage input pairing vertex) := by
  by_cases hAt : vertex.1.1 = wall
  · obtain ⟨sourceBlock, hVertex⟩ :=
      exists_wallBlock_sourceVertex data wall vertex hAt
    subst hVertex
    rw [branchImage_wall]
    cases hPicture : input.blockPicture sourceBlock with
    | dangling old_dangling =>
        rw [dangling_old_nonDanglingValency data star sourceBlock old_dangling]
          at hBranch
        omega
    | nd2 block picture =>
        rw [nd2_old_nonDanglingValency picture] at hBranch
        omega
    | nd3 block picture =>
        rw [branchSide_nd3 input pairing sourceBlock block picture hPicture]
        have hVal : nonDanglingValency (member input pairing).datum
            (sideEndpoint input pairing
              (! W4TargetPairings.Pairing.labelRight pairing
                (block.singletonLabel pairing)) sourceBlock.1) = 3 :=
          nd3_otherSide_nonDanglingValency input pairing sourceBlock block
            picture hPicture sourceBlock.1 rfl
        omega
  · rw [branchImage_away input pairing vertex hAt,
      nonDanglingValency_retainedVertex (member input pairing) input.valid
        (member_sourceGenus input pairing) vertex hAt]
    exact hBranch

/-- The branch-vertex map of an outgoing W4 candidate. -/
noncomputable def branchVertexMap (input : AuxR0SourceInput data star)
    (pairing : Fin 3)
    (vertex : BranchVertex data) : BranchVertex (member input pairing).datum :=
  ⟨branchImage input pairing vertex.1,
    three_le_branchImage input pairing vertex.1 vertex.2⟩


omit [DecidableEq target.edges] in
theorem sideVertex_inj {first second : Bool}
    (hEq : sideVertex target wall first = sideVertex target wall second) :
    first = second := by
  cases first <;> cases second <;>
    simp_all [sideVertex, oldVertex, freshVertex]

theorem branchImage_injective (input : AuxR0SourceInput data star)
    (pairing : Fin 3) : Function.Injective (branchImage input pairing) := by
  intro first second hEq
  by_cases hFirst : first.1.1 = wall <;> by_cases hSecond : second.1.1 = wall
  · rw [branchImage, ite_eq_left hFirst, branchImage, ite_eq_left hSecond] at hEq
    have hSide := sideVertex_inj
      (congrArg (fun vertex : (member input pairing).datum.SourceVertex ↦
        vertex.1.1) hEq)
    rw [hSide] at hEq
    have hRel := (sideEndpoint_eq_iff input pairing _ first.1.2
      second.1.2).mp hEq
    have hWall := (sidePartition_refines_wall data star
      input.activeProfile.blockPattern pairing _).rel hRel
    refine Subtype.ext (Prod.ext (hFirst.trans hSecond.symm) ?_)
    have hFirstRepr : (data.vertexPartition wall).repr first.1.2 = first.1.2 :=
      hFirst ▸ first.2
    have hSecondRepr : (data.vertexPartition wall).repr second.1.2 =
        second.1.2 := hSecond ▸ second.2
    exact hFirstRepr.symm.trans (hWall.trans hSecondRepr)
  · rw [branchImage, ite_eq_left hFirst, branchImage, ite_eq_right hSecond] at hEq
    have hTarget : sideVertex target wall
          (branchSide input pairing (WallBlock.ofSheet data wall first.1.2)) =
        oldVertex target second.1.1 :=
      congrArg (fun vertex : (member input pairing).datum.SourceVertex ↦
        vertex.1.1) hEq
    cases hSide : branchSide input pairing
        (WallBlock.ofSheet data wall first.1.2) with
    | false =>
        rw [hSide, sideVertex_false] at hTarget
        exact absurd (Sum.inl.inj hTarget).symm hSecond
    | true =>
        rw [hSide, sideVertex_true] at hTarget
        have hAbsurd : (Sum.inr () : Vertex target) = Sum.inl second.1.1 :=
          hTarget
        simp at hAbsurd
  · rw [branchImage, ite_eq_right hFirst, branchImage, ite_eq_left hSecond] at hEq
    have hTarget : oldVertex target first.1.1 = sideVertex target wall
        (branchSide input pairing (WallBlock.ofSheet data wall second.1.2)) :=
      congrArg (fun vertex : (member input pairing).datum.SourceVertex ↦
        vertex.1.1) hEq
    cases hSide : branchSide input pairing
        (WallBlock.ofSheet data wall second.1.2) with
    | false =>
        rw [hSide, sideVertex_false] at hTarget
        exact absurd (Sum.inl.inj hTarget) hFirst
    | true =>
        rw [hSide, sideVertex_true] at hTarget
        have hAbsurd : (Sum.inl first.1.1 : Vertex target) = Sum.inr () :=
          hTarget
        simp at hAbsurd
  · rw [branchImage, ite_eq_right hFirst, branchImage, ite_eq_right hSecond] at hEq
    exact ResolutionStableIncidence.retainedVertex_injective_away
      (member input pairing) first second hFirst hSecond hEq

theorem branchVertexMap_injective (input : AuxR0SourceInput data star)
    (pairing : Fin 3) : Function.Injective (branchVertexMap input pairing) :=
  fun _ _ hEq ↦ Subtype.ext
    (branchImage_injective input pairing (congrArg Subtype.val hEq))

theorem branchVertexMap_surjective (input : AuxR0SourceInput data star)
    (pairing : Fin 3) : Function.Surjective (branchVertexMap input pairing) := by
  intro branch
  have hSelf : (member input pairing).datum.sourceEndpoint branch.1.1.1
      branch.1.1.2 = branch.1 :=
    ((member input pairing).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  have hWallCase : ∀ (side : Bool) (sheet : Fin degree),
      sideEndpoint input pairing side sheet = branch.1 →
      ∃ vertex, branchVertexMap input pairing vertex = branch := by
    intro side sheet hEndpoint
    have hBranch : 3 ≤ nonDanglingValency (member input pairing).datum
        (sideEndpoint input pairing side sheet) := by
      rw [hEndpoint]; exact branch.2
    obtain ⟨block, picture, hPicture, hSideEq⟩ :=
      branch_sideEndpoint input pairing side sheet hBranch
    refine ⟨⟨WallBlock.sourceVertex data wall (WallBlock.ofSheet data wall sheet),
      le_of_eq (nd3_old_nonDanglingValency picture).symm⟩, ?_⟩
    apply Subtype.ext
    show branchImage input pairing _ = branch.1
    rw [branchImage_wall, branchSide_nd3 input pairing _ block picture hPicture,
      ← hSideEq, ← hEndpoint]
    refine (sideEndpoint_eq_iff input pairing side _ sheet).mpr ?_
    rw [hSideEq]
    exact nd3_otherSide_rel input pairing _ block picture hPicture sheet
      (rel_ofSheet data wall sheet)
  cases hTarget : branch.1.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        exact hWallCase false branch.1.1.2 ((congrArg (fun place ↦
          (member input pairing).datum.sourceEndpoint place branch.1.1.2)
          hTarget.symm).trans hSelf)
      · obtain ⟨old, hOld, hVertex⟩ := exists_retainedVertex_of_target
          (member input pairing) branch.1 place hAt hTarget
        have hAway : old.1.1 ≠ wall := hOld ▸ hAt
        have hValency := nonDanglingValency_retainedVertex
          (member input pairing) input.valid (member_sourceGenus input pairing)
          old hAway
        refine ⟨⟨old, ?_⟩, ?_⟩
        · have hBranch := branch.2
          rw [← hVertex, hValency] at hBranch
          exact hBranch
        · exact Subtype.ext
            ((branchImage_away input pairing old hAway).trans hVertex)
  | inr point =>
      cases point
      exact hWallCase true branch.1.1.2 ((congrArg (fun place ↦
        (member input pairing).datum.sourceEndpoint place branch.1.1.2)
        hTarget.symm).trans hSelf)

/-- **The branch-vertex equivalence of an outgoing W4 candidate.** -/
noncomputable def branchVertexEquiv (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    BranchVertex data ≃ BranchVertex (member input pairing).datum :=
  Equiv.ofBijective (branchVertexMap input pairing)
    ⟨branchVertexMap_injective input pairing,
      branchVertexMap_surjective input pairing⟩


/-! ## The branch/row incidence equivalence -/

/-- The canonical incoming occurrence of the isolated nd3 branch, named once. -/
noncomputable def nd3SingletonEdge {sourceBlock : WallBlock data wall}
    {block : Nd3Block} (picture : AuxR0Nd3Picture data star sourceBlock block)
    (pairing : Fin 3) : NonDanglingEdge data :=
  branchEdge data star (block.singletonLabel pairing)
    (picture.activeSheet (block.singletonLabel pairing))
    (picture.active_survives _ (block.singletonLabel_mem_activeLabels pairing))

/-- The surviving regrown occurrence above an nd3 block shares its outgoing row
with the retained copy of the isolated branch's own occurrence. -/
theorem nd3_regrown_stablePath (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture) :
    (retained input pairing (nd3SingletonEdge picture pairing)).stablePath =
      (regrownEdge input pairing
        (picture.activeSheet (block.singletonLabel pairing))
        (nd3_new_survives_activeSheet input pairing sourceBlock block picture
          hPicture)).stablePath := by
  refine Eq.trans (congrArg (fun edge : NonDanglingEdge data ↦
    (retained input pairing edge).stablePath) (Subtype.ext ?_))
    (regrown_stablePath_eq input pairing _ (nd3_new_survives_activeSheet input
      pairing sourceBlock block picture hPicture))
  show (nd3SingletonEdge picture pairing).1 = newOldSourceEdge input pairing _
  refine Eq.symm (Eq.trans (congrArg (blockOldSourceEdge input pairing)
    (WallBlock.ofSheet_eq_of_rel data wall sourceBlock _
      (picture.active_sheet _ (block.singletonLabel_mem_activeLabels pairing))))
    ?_)
  exact blockOldSourceEdge_nd3 input pairing sourceBlock block picture hPicture

/-- **The trivalent nd3 branch keeps every row multiplicity.**  Its three
surviving incoming occurrences are matched with the two retained branch
occurrences and the regrown occurrence; a row carried twice at the old branch
is carried twice at the new one. -/
theorem incidenceCount_nd3_branch (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (picture : AuxR0Nd3Picture data star sourceBlock block)
    (hPicture : input.blockPicture sourceBlock = .nd3 block picture)
    (path : StablePath data) :
    incidenceCount data (WallBlock.sourceVertex data wall sourceBlock) path =
      incidenceCount (member input pairing).datum
        (sideEndpoint input pairing
          (! W4TargetPairings.Pairing.labelRight pairing
            (block.singletonLabel pairing)) sourceBlock.1)
        (stablePathEquiv input pairing path) := by
  classical
  have hActive := block.singletonLabel_mem_activeLabels pairing
  have hRegSurvives := nd3_new_survives_activeSheet input pairing sourceBlock
    block picture hPicture
  have hRegRow := nd3_regrown_stablePath input pairing sourceBlock block picture
    hPicture
  have hCensus := nd3_otherSide_census input pairing sourceBlock block picture
    hPicture sourceBlock.1 (rfl : (data.vertexPartition wall).Rel sourceBlock.1
      sourceBlock.1)
  unfold incidenceCount
  refine Finset.card_bij (fun edge _ ↦
    if edge.1 = (nd3SingletonEdge picture pairing).1 then
      regrownEdge input pairing
        (picture.activeSheet (block.singletonLabel pairing)) hRegSurvives
    else retained input pairing edge) ?_ ?_ ?_
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    obtain ⟨hIncident, hRow⟩ := hEdge
    by_cases hIsSingleton : edge.1 = (nd3SingletonEdge picture pairing).1
    · rw [ite_eq_left hIsSingleton]
      refine ⟨((mem_nonDanglingIncident _ _ _).mp
        ((hCensus _).mpr (Or.inr rfl))).2, ?_⟩
      rw [← hRegRow, ← hRow, stablePathEquiv_mk,
        show edge = nd3SingletonEdge picture pairing from
          Subtype.ext hIsSingleton]
    · rw [ite_eq_right hIsSingleton]
      obtain ⟨hBlock, hLabelled⟩ :=
        old_survivor_info data star sourceBlock edge.1 hIncident
      obtain ⟨label, hLabelActive, hEdgeValue⟩ :=
        picture.only_surviving edge.1 hBlock hLabelled edge.2
      have hSideNe : W4TargetPairings.Pairing.labelRight pairing label ≠
          W4TargetPairings.Pairing.labelRight pairing
            (block.singletonLabel pairing) := by
        intro hSame
        exact hIsSingleton (hEdgeValue.trans (congrArg
          (fun other ↦ data.sourceEdge (star.edge other)
            (picture.activeSheet other))
          (block.eq_singletonLabel_of_active_of_same_side pairing label
            ((block.mem_activeLabels label).mp hLabelActive) hSame)))
      refine ⟨((mem_nonDanglingIncident _ _ _).mp ((hCensus _).mpr
        (Or.inl ⟨label, hLabelActive, hSideNe, congrArg
          (member input pairing).oldSourceEdge hEdgeValue⟩))).2, ?_⟩
      rw [← hRow, stablePathEquiv_mk]
  · intro first hFirst second hSecond hEq
    by_cases hFirstSingleton : first.1 = (nd3SingletonEdge picture pairing).1 <;>
      by_cases hSecondSingleton :
        second.1 = (nd3SingletonEdge picture pairing).1
    · exact Subtype.ext (hFirstSingleton.trans hSecondSingleton.symm)
    · rw [ite_eq_left hFirstSingleton, ite_eq_right hSecondSingleton] at hEq
      exact absurd (congrArg Subtype.val hEq).symm
        (oldSourceEdge_ne_newSourceEdge (member input pairing) _ _)
    · rw [ite_eq_right hFirstSingleton, ite_eq_left hSecondSingleton] at hEq
      exact absurd (congrArg Subtype.val hEq)
        (oldSourceEdge_ne_newSourceEdge (member input pairing) _ _)
    · rw [ite_eq_right hFirstSingleton, ite_eq_right hSecondSingleton] at hEq
      exact retained_injective input pairing hEq
  · intro edge hEdge
    simp only [Finset.mem_filter, mem_incidentEdges] at hEdge
    obtain ⟨hIncident, hRow⟩ := hEdge
    rcases (hCensus edge.1).mp ((mem_nonDanglingIncident _ _ _).mpr
        ⟨edge.2, hIncident⟩) with
      ⟨label, hLabelActive, hSideNe, hValue⟩ | hValue
    · have hSurvives := picture.active_survives label hLabelActive
      have hEdgeEq : edge =
          retained input pairing (branchEdge data star label
            (picture.activeSheet label) hSurvives) := Subtype.ext hValue
      have hNotSingleton : (branchEdge data star label
          (picture.activeSheet label) hSurvives).1 ≠
          (nd3SingletonEdge picture pairing).1 := by
        intro hSame
        exact hSideNe (congrArg (W4TargetPairings.Pairing.labelRight pairing)
          (star.edge_injective
            (congrArg (fun e : data.SourceEdge ↦ e.1.1) hSame)))
      refine ⟨branchEdge data star label (picture.activeSheet label) hSurvives,
        ?_, ?_⟩
      · simp only [Finset.mem_filter, mem_incidentEdges]
        refine ⟨branch_incident_wallVertex data star sourceBlock label _
          (picture.active_sheet label hLabelActive),
          (stablePathEquiv input pairing).injective ?_⟩
        rw [stablePathEquiv_mk, ← hRow, hEdgeEq]
      · rw [ite_eq_right hNotSingleton]
        exact hEdgeEq.symm
    · refine ⟨nd3SingletonEdge picture pairing, ?_, ?_⟩
      · simp only [Finset.mem_filter, mem_incidentEdges]
        refine ⟨branch_incident_wallVertex data star sourceBlock _ _
          (picture.active_sheet _ hActive),
          (stablePathEquiv input pairing).injective ?_⟩
        rw [stablePathEquiv_mk, hRegRow, ← hRow]
        exact congrArg NonDanglingEdge.stablePath (Subtype.ext hValue).symm
      · rw [ite_eq_left rfl]
        exact (Subtype.ext hValue).symm

/-- **The occurrence-induced branch/row incidence equivalence of an outgoing W4
candidate.**  Branch vertices are matched geometrically and every branch/row
incidence multiplicity is preserved. -/
noncomputable def equivalence (input : AuxR0SourceInput data star)
    (pairing : Fin 3) :
    StableGraphIncidence.Equivalence data (member input pairing).datum where
  vertex := branchVertexEquiv input pairing
  row := stablePathEquiv input pairing
  incidence branch path := by
    by_cases hAt : branch.1.1.1 = wall
    · obtain ⟨sourceBlock, hVertex⟩ :=
        exists_wallBlock_sourceVertex data wall branch.1 hAt
      have hBranch := branch.2
      rw [← hVertex] at hBranch ⊢
      cases hPicture : input.blockPicture sourceBlock with
      | dangling old_dangling =>
          rw [dangling_old_nonDanglingValency data star sourceBlock old_dangling]
            at hBranch
          omega
      | nd2 block picture =>
          rw [nd2_old_nonDanglingValency picture] at hBranch
          omega
      | nd3 block picture =>
          have hImage : (branchVertexEquiv input pairing branch).1 =
              sideEndpoint input pairing
                (! W4TargetPairings.Pairing.labelRight pairing
                  (block.singletonLabel pairing)) sourceBlock.1 := by
            show branchImage input pairing branch.1 = _
            rw [← hVertex, branchImage_wall,
              branchSide_nd3 input pairing sourceBlock block picture hPicture]
          rw [hImage]
          exact incidenceCount_nd3_branch input pairing sourceBlock block
            picture hPicture path
    · have hImage : (branchVertexEquiv input pairing branch).1 =
          retainedVertex (member input pairing) branch.1 := by
        show branchImage input pairing branch.1 = _
        exact branchImage_away input pairing branch.1 hAt
      rw [hImage]
      exact ResolutionStableIncidence.incidenceCount_retainedVertex
        (member input pairing) input.valid (member_sourceGenus input pairing)
        (stablePathEquiv input pairing)
        (stablePathEquiv_mk input pairing) branch.1 hAt path

theorem equivalence_row (input : AuxR0SourceInput data star) (pairing : Fin 3) :
    (equivalence input pairing).row = stablePathEquiv input pairing := rfl

/-- A stable source with path ends keeps them in every outgoing W4
candidate. -/
theorem hasPathEnds (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (hEnds : HasPathEnds data) : HasPathEnds (member input pairing).datum :=
  (equivalence input pairing).hasPathEnds input.valid.1 hEnds


/-! ## The honest natural stable-length matrix: the retained columns

This is the limit-matrix lemma of Draisma--Vargas Part I
(`lemma-limit-matrix-change`) for the W4 wall: under the occurrence-induced row
equivalence every column of an outgoing
candidate other than the regrown one is literally the incoming wall column.
The regrown column is not evaluated here.
-/

theorem occurrences_retained (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (path : StablePath data) (place : target.edges) :
    occurrences (member input pairing).datum
        (stablePathEquiv input pairing path)
        (occurrenceEquiv target wall (member input pairing).right (some place)) =
      (occurrences data path place).image
        (member input pairing).oldSourceEdge := by
  classical
  ext edge
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (member input pairing) edge with
      ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hOld : ¬ IsDangling data old := fun hDangling ↦ hSurvives
        ((ResolutionPruning.isDangling_oldSourceEdge_iff (member input pairing)
          input.valid (member_sourceGenus input pairing) old).mpr hDangling)
      refine Finset.mem_image.mpr ⟨old, (mem_occurrences _ _ _).mpr
        ⟨⟨hOld, ?_⟩, ?_⟩, rfl⟩
      · exact (stablePathEquiv input pairing).injective
          ((stablePathEquiv_mk input pairing ⟨old, hOld⟩).trans hRow)
      · exact Option.some.inj ((occurrenceEquiv target wall
          (member input pairing).right).injective hTarget)
    · have hLabels := (occurrenceEquiv target wall
        (member input pairing).right).injective hTarget
      cases hLabels
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    refine (mem_occurrences _ _ _).mpr ⟨⟨ResolutionSurvival.not_isDangling_oldSourceEdge
      (member input pairing) input.valid.1 old hSurvives, ?_⟩, ?_⟩
    · exact (stablePathEquiv_mk input pairing ⟨old, hSurvives⟩).symm.trans
        (congrArg (stablePathEquiv input pairing) hRow)
    · exact congrArg (fun label ↦ occurrenceEquiv target wall
        (member input pairing).right (some label)) hTarget

/-- **Every retained column of an outgoing W4 candidate is the incoming wall
column.**  Indices are preserved literally by retention, and the row map is
the proved occurrence-induced equivalence. -/
theorem matrix_retained (input : AuxR0SourceInput data star) (pairing : Fin 3)
    (path : StablePath data) (place : target.edges) :
    matrix (member input pairing).datum (stablePathEquiv input pairing path)
        (occurrenceEquiv target wall (member input pairing).right (some place)) =
      matrix data path place := by
  classical
  unfold matrix
  rw [occurrences_retained, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
  · intro first _ second _ hEqual
    exact ResolutionCut.oldSourceEdge_injective _ hEqual

/-- The regrown column is supported on the surviving regrown occurrences, and
each of them sits on the outgoing row of the canonical incoming occurrence of
its own wall block. -/
theorem mem_occurrences_new_iff (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (path : StablePath data)
    (edge : (member input pairing).datum.SourceEdge) :
    edge ∈ occurrences (member input pairing).datum
        (stablePathEquiv input pairing path)
        (occurrenceEquiv target wall (member input pairing).right none) ↔
      ∃ (sheet : Fin degree) (hSurvives : ¬ IsDangling (member input pairing).datum
          ((member input pairing).newSourceEdge sheet)),
        edge = (member input pairing).newSourceEdge sheet ∧
          (newOldEdge input pairing sheet hSurvives).stablePath = path := by
  classical
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    rcases ResolutionPruning.sourceEdge_cases (member input pairing) edge with
      ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hLabels := (occurrenceEquiv target wall
        (member input pairing).right).injective hTarget
      exact absurd hLabels (by simp)
    · refine ⟨sheet, hSurvives, rfl, (stablePathEquiv input pairing).injective ?_⟩
      rw [stablePathEquiv_mk]
      exact (regrown_stablePath_eq input pairing sheet hSurvives).trans hRow
  · rintro ⟨sheet, hSurvives, rfl, hRow⟩
    refine ⟨⟨hSurvives, ?_⟩, rfl⟩
    rw [← hRow, stablePathEquiv_mk]
    exact (regrown_stablePath_eq input pairing sheet hSurvives).symm

end Candidate

end DraismaVargas.LocalCases.W4OutgoingStableRows
