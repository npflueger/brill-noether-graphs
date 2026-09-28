import DraismaVargas.LocalCases.W2R1SourceProfile

/-!
# Actual ramification-two, nd3 occurrence profiles at a divalent wall

Source: Draisma--Vargas Part I, Case {w2-r2-nd3} and Figures 32--35.
Refinement gives the two alternatives
`k₁ + k₂ = |A₀| = k₃ + 1` (M) and
`k₁ + k₂ + 1 = |A₀| = k₃` (P).

The hypotheses are `SecondEquation.W2SourceInput`, an actual
wall block with local ramification two, and the explicit additional assumption
that its non-dangling valency is three.  We do not derive that last assumption:
the source's nd2 exclusions require further inherited full-rank information.
`W2IncomingClassification.exists_classification` supplies it for actual
full-dimensional forest contractions and consumes this profile.

Four incident occurrences and three survivors give one dangling occurrence,
of index one.  Each target direction has total index equal to the block size,
which is at least two.  Therefore each direction contains a survivor, and the
surviving occurrences split two-plus-one over the supplied actual two-star.
The dangling occurrence's target direction distinguishes M from P.
No outgoing resolution, stable-row census, or determinant identity is assumed
or claimed here.
-/

namespace DraismaVargas.LocalCases.W2R2SourceProfile

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open W2R1SourceProfile

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-- The unique deleted occurrence, named among the actual incident source
occurrences rather than merely represented by an index. -/
structure DeletedOccurrence (data : GluingDatum target degree)
    (block : WallBlock data wall) where
  edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  dangling : IsDangling data edge.1
  index_one : data.sourceEdgeIndex edge.1 = 1
  unique : ∀ other : IncidentSourceEdge data (WallBlock.sourceVertex data wall block),
    IsDangling data other.1 ↔ other = edge

theorem exists_deletedOccurrence {data : GluingDatum target degree}
    {star : TwoStar target wall} (input : W2SourceInput data star)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3) :
    Nonempty (DeletedOccurrence data block) := by
  classical
  have hCard := W2SourceInput.card_incidentSourceEdge_wallBlock (data := data) star block
  rw [hR] at hCard
  have hSplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block))))
    (p := fun edge ↦ IsDangling data edge.1)
  rw [card_filter_not_isDangling_eq_nonDanglingValency, hNd, Finset.card_univ] at hSplit
  have hOne : ((Finset.univ : Finset (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block))).filter
        (fun edge ↦ IsDangling data edge.1)).card = 1 := by omega
  obtain ⟨edge, hOnly⟩ := Finset.card_eq_one.mp hOne
  have hDangling : IsDangling data edge.1 := by
    have hMem : edge ∈ ((Finset.univ : Finset (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block))).filter
        (fun other ↦ IsDangling data other.1)) := by rw [hOnly]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hMem).2
  refine ⟨⟨edge, hDangling, input.dangling_no_glue edge.1 hDangling, ?_⟩⟩
  intro other
  have hMem := Finset.ext_iff.mp hOnly other
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton] using hMem

/-- Four positive occurrences require local degree at least two. -/
theorem two_le_blockCard (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 2) :
    2 ≤ (data.vertexPartition wall).blockCard block.1 := by
  have hCard := W2SourceInput.card_incidentSourceEdge_wallBlock (data := data) star block
  rw [hR] at hCard
  have hSum := sum_sourceEdgeIndex_incident data (WallBlock.sourceVertex data wall block)
  have hLe : (Fintype.card (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block)) : ℤ) ≤
      ∑ edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block),
        (data.sourceEdgeIndex edge.1 : ℤ) := by
    calc
      (Fintype.card (IncidentSourceEdge data
          (WallBlock.sourceVertex data wall block)) : ℤ) =
          ∑ _edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block),
            (1 : ℤ) := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun edge _ ↦ by
        exact_mod_cast sourceEdgeIndex_pos data edge.1
  have hTarget : (GluingDatum.incidentEdges
      (WallBlock.sourceVertex data wall block).1.1).card = 2 := star.card_incidentEdges
  have hBlock : (data.vertexPartition (WallBlock.sourceVertex data wall block).1.1).blockCard
      (WallBlock.sourceVertex data wall block).1.2 =
        (data.vertexPartition wall).blockCard block.1 := by
    simp only [WallBlock.sourceVertex, GluingDatum.sourceEndpoint, block.2]
  rw [hTarget, hBlock] at hSum
  omega

/-- The surviving part of the actual source fibre over a named direction. -/
noncomputable def survivingFibre (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) (label : Fin 2) :
    Finset (IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :=
  (fibre data star block label).filter fun edge ↦ ¬ IsDangling data edge.1

namespace survivingFibre

variable (data : GluingDatum target degree) (star : TwoStar target wall)
  (block : WallBlock data wall)

theorem mem (label : Fin 2)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    edge ∈ survivingFibre data star block label ↔
      edge.1.1.1 = star.edge label ∧ ¬ IsDangling data edge.1 := by
  rw [survivingFibre, Finset.mem_filter, fibre.mem]

theorem nonempty (deleted : DeletedOccurrence data block)
    (hSize : 2 ≤ (data.vertexPartition wall).blockCard block.1) (label : Fin 2) :
    (survivingFibre data star block label).Nonempty := by
  classical
  by_contra hEmpty
  have hAll : ∀ edge ∈ fibre data star block label, edge = deleted.edge := by
    intro edge hMem
    apply (deleted.unique edge).mp
    by_contra hSurvives
    exact hEmpty ⟨edge, (mem data star block label edge).mpr
      ⟨(fibre.mem data star block label edge).mp hMem, hSurvives⟩⟩
  obtain ⟨edge, hMem⟩ := fibre.nonempty data star block label
  have hEq : fibre data star block label = {deleted.edge} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hAll edge hMem ▸ hMem, hAll⟩
  have hSum := fibre.sum_index data star block label
  rw [hEq, Finset.sum_singleton, deleted.index_one] at hSum
  omega

theorem union : survivingFibre data star block 0 ∪ survivingFibre data star block 1 =
    (Finset.univ : Finset (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block))).filter
        (fun edge ↦ ¬ IsDangling data edge.1) := by
  classical
  rw [survivingFibre, survivingFibre, ← Finset.filter_union, fibre.union]

theorem disjoint :
    Disjoint (survivingFibre data star block 0) (survivingFibre data star block 1) := by
  classical
  exact (fibre.disjoint data star block).mono (Finset.filter_subset _ _)
    (Finset.filter_subset _ _)

theorem card_add_eq_three
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3) :
    (survivingFibre data star block 0).card + (survivingFibre data star block 1).card = 3 := by
  have hUnion := Finset.card_union_of_disjoint (disjoint data star block)
  rw [union, card_filter_not_isDangling_eq_nonDanglingValency, hNd] at hUnion
  exact hUnion.symm

end survivingFibre

/-- Reinsert the unique dangling occurrence in its actual direction. -/
theorem fibre_eq_insert_survivingFibre (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall)
    (deleted : DeletedOccurrence data block) (label : Fin 2)
    (hTarget : deleted.edge.1.1.1 = star.edge label) :
    fibre data star block label =
      insert deleted.edge (survivingFibre data star block label) := by
  classical
  ext edge
  rw [fibre.mem, Finset.mem_insert, survivingFibre.mem]
  constructor
  · intro hEdgeTarget
    by_cases hDangling : IsDangling data edge.1
    · exact Or.inl ((deleted.unique edge).mp hDangling)
    · exact Or.inr ⟨hEdgeTarget, hDangling⟩
  · rintro (rfl | hEdge)
    · exact hTarget
    · exact hEdge.1

/-- The direction not carrying the deleted occurrence is already its entire
surviving fibre. -/
theorem fibre_eq_survivingFibre (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall)
    (deleted : DeletedOccurrence data block) (label : Fin 2)
    (hTarget : deleted.edge.1.1.1 ≠ star.edge label) :
    fibre data star block label = survivingFibre data star block label := by
  classical
  ext edge
  rw [fibre.mem, survivingFibre.mem]
  constructor
  · intro hEdgeTarget
    refine ⟨hEdgeTarget, ?_⟩
    intro hDangling
    have hEq := (deleted.unique edge).mp hDangling
    subst edge
    exact hTarget hEdgeTarget
  · exact And.left

/-- The source's M/P profiles, attached to four actual occurrences.  The
surviving fibre identities retain the complete occurrence census in each
direction; the fourth occurrence is uniquely dangling. -/
structure SourceProfile (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) where
  ramification : data.localRamification wall block = 2
  valency : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3
  doubleLabel : Fin 2
  singleLabel : Fin 2
  labels_ne : doubleLabel ≠ singleLabel
  first : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  second : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  third : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  deleted : DeletedOccurrence data block
  first_ne_second : first ≠ second
  first_target : first.1.1.1 = star.edge doubleLabel
  second_target : second.1.1.1 = star.edge doubleLabel
  third_target : third.1.1.1 = star.edge singleLabel
  first_survives : ¬ IsDangling data first.1
  second_survives : ¬ IsDangling data second.1
  third_survives : ¬ IsDangling data third.1
  double_fibre : survivingFibre data star block doubleLabel = {first, second}
  single_fibre : survivingFibre data star block singleLabel = {third}
  exhaustive : ∀ edge, edge = first ∨ edge = second ∨ edge = third ∨ edge = deleted.edge
  cases :
    (deleted.edge.1.1.1 = star.edge singleLabel ∧
      data.sourceEdgeIndex first.1 + data.sourceEdgeIndex second.1 =
        (data.vertexPartition wall).blockCard block.1 ∧
      data.sourceEdgeIndex third.1 + 1 = (data.vertexPartition wall).blockCard block.1) ∨
    (deleted.edge.1.1.1 = star.edge doubleLabel ∧
      data.sourceEdgeIndex first.1 + data.sourceEdgeIndex second.1 + 1 =
        (data.vertexPartition wall).blockCard block.1 ∧
      data.sourceEdgeIndex third.1 = (data.vertexPartition wall).blockCard block.1)

/-- The explicit ramification-two and nd3 hypotheses yield the source's
complete M/P occurrence profile.  Surviving valency three is an input, not a
consequence asserted by this theorem. -/
theorem exists_sourceProfile {data : GluingDatum target degree}
    {star : TwoStar target wall} (input : W2SourceInput data star)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3) :
    Nonempty (SourceProfile data star block) := by
  classical
  obtain ⟨deleted⟩ := exists_deletedOccurrence input block hR hNd
  have hSize := two_le_blockCard data star block hR
  have hCount := survivingFibre.card_add_eq_three data star block hNd
  have hZeroPos := Finset.card_pos.mpr
    (survivingFibre.nonempty data star block deleted hSize 0)
  have hOnePos := Finset.card_pos.mpr
    (survivingFibre.nonempty data star block deleted hSize 1)
  have hShape : ∃ doubleLabel singleLabel : Fin 2, doubleLabel ≠ singleLabel ∧
      (survivingFibre data star block doubleLabel).card = 2 ∧
      (survivingFibre data star block singleLabel).card = 1 := by
    by_cases hZero : (survivingFibre data star block 0).card = 2
    · exact ⟨0, 1, by decide, hZero, by omega⟩
    · exact ⟨1, 0, by decide, by omega, by omega⟩
  obtain ⟨doubleLabel, singleLabel, hLabels, hDouble, hSingle⟩ := hShape
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hDouble
  obtain ⟨third, hThird⟩ := Finset.card_eq_one.mp hSingle
  have hFirstMem : first ∈ survivingFibre data star block doubleLabel := by simp [hPair]
  have hSecondMem : second ∈ survivingFibre data star block doubleLabel := by simp [hPair]
  have hThirdMem : third ∈ survivingFibre data star block singleLabel := by simp [hThird]
  obtain ⟨hFirstTarget, hFirstSurvives⟩ :=
    (survivingFibre.mem data star block doubleLabel first).mp hFirstMem
  obtain ⟨hSecondTarget, hSecondSurvives⟩ :=
    (survivingFibre.mem data star block doubleLabel second).mp hSecondMem
  obtain ⟨hThirdTarget, hThirdSurvives⟩ :=
    (survivingFibre.mem data star block singleLabel third).mp hThirdMem
  have hLabelCases : ∀ label : Fin 2, label = doubleLabel ∨ label = singleLabel := by
    intro label
    omega
  have hTargetCases : ∀ edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block),
      edge.1.1.1 = star.edge doubleLabel ∨ edge.1.1.1 = star.edge singleLabel := by
    intro edge
    have hIncident := (incident_iff_target_mem_and_rel data edge.1 _).mp edge.2 |>.1
    let label := star.label.symm ⟨edge.1.1.1, hIncident⟩
    have hTarget : star.edge label = edge.1.1.1 :=
      congrArg Subtype.val (star.label.apply_symm_apply ⟨edge.1.1.1, hIncident⟩)
    rcases hLabelCases label with hDouble | hSingle
    · exact Or.inl (hDouble ▸ hTarget.symm)
    · exact Or.inr (hSingle ▸ hTarget.symm)
  have hDeletedNotMem : ∀ label, deleted.edge ∉ survivingFibre data star block label := by
    intro label hMem
    exact ((survivingFibre.mem data star block label deleted.edge).mp hMem).2 deleted.dangling
  refine ⟨{
    ramification := hR
    valency := hNd
    doubleLabel := doubleLabel
    singleLabel := singleLabel
    labels_ne := hLabels
    first := first
    second := second
    third := third
    deleted := deleted
    first_ne_second := hNe
    first_target := hFirstTarget
    second_target := hSecondTarget
    third_target := hThirdTarget
    first_survives := hFirstSurvives
    second_survives := hSecondSurvives
    third_survives := hThirdSurvives
    double_fibre := hPair
    single_fibre := hThird
    exhaustive := ?_
    cases := ?_ }⟩
  · intro edge
    by_cases hDangling : IsDangling data edge.1
    · exact Or.inr (Or.inr (Or.inr ((deleted.unique edge).mp hDangling)))
    · rcases hTargetCases edge with hDouble | hSingle
      · have hMem := (survivingFibre.mem data star block doubleLabel edge).mpr
          ⟨hDouble, hDangling⟩
        rw [hPair] at hMem
        rcases Finset.mem_insert.mp hMem with hFirst | hSecond
        · exact Or.inl hFirst
        · exact Or.inr (Or.inl (Finset.mem_singleton.mp hSecond))
      · have hMem := (survivingFibre.mem data star block singleLabel edge).mpr
          ⟨hSingle, hDangling⟩
        rw [hThird] at hMem
        exact Or.inr (Or.inr (Or.inl (Finset.mem_singleton.mp hMem)))
  · have hDoubleSum := fibre.sum_index data star block doubleLabel
    have hSingleSum := fibre.sum_index data star block singleLabel
    have hTargetNe := star.edge_injective.ne hLabels
    rcases hTargetCases deleted.edge with hDeletedDouble | hDeletedSingle
    · have hDeletedNeSingle : deleted.edge.1.1.1 ≠ star.edge singleLabel :=
        fun h ↦ hTargetNe (hDeletedDouble.symm.trans h)
      rw [fibre_eq_insert_survivingFibre data star block deleted doubleLabel hDeletedDouble,
        Finset.sum_insert (hDeletedNotMem doubleLabel), deleted.index_one,
        hPair, Finset.sum_pair hNe] at hDoubleSum
      rw [fibre_eq_survivingFibre data star block deleted singleLabel hDeletedNeSingle,
        hThird, Finset.sum_singleton] at hSingleSum
      right
      refine ⟨hDeletedDouble, ?_, ?_⟩ <;> omega
    · have hDeletedNeDouble : deleted.edge.1.1.1 ≠ star.edge doubleLabel :=
        fun h ↦ hTargetNe (h.symm.trans hDeletedSingle)
      rw [fibre_eq_survivingFibre data star block deleted doubleLabel hDeletedNeDouble,
        hPair, Finset.sum_pair hNe] at hDoubleSum
      rw [fibre_eq_insert_survivingFibre data star block deleted singleLabel hDeletedSingle,
        Finset.sum_insert (hDeletedNotMem singleLabel), deleted.index_one,
        hThird, Finset.sum_singleton] at hSingleSum
      left
      refine ⟨hDeletedSingle, ?_, ?_⟩ <;> omega

namespace SourceProfile

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}

/-- The four displayed occurrences exhaust the literal incident-edge type. -/
theorem incident_univ (profile : SourceProfile data star block) :
    (Finset.univ : Finset (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block))) =
        {profile.first, profile.second, profile.third, profile.deleted.edge} := by
  ext edge
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact profile.exhaustive edge

/-- The index-only consequences used to select the M and P resolutions.
The stronger `cases` field also records which actual direction contains the
dangling occurrence and both equations involving the local degree. -/
theorem index_balance (profile : SourceProfile data star block) :
    data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 =
        data.sourceEdgeIndex profile.third.1 + 1 ∨
      data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 + 1 =
        data.sourceEdgeIndex profile.third.1 := by
  rcases profile.cases with ⟨_, hPair, hSingle⟩ | ⟨_, hPair, hSingle⟩
  · exact Or.inl (hPair.trans hSingle.symm)
  · exact Or.inr (hPair.trans hSingle.symm)

end SourceProfile

end DraismaVargas.LocalCases.W2R2SourceProfile
