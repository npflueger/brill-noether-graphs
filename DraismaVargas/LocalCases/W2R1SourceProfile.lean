import DraismaVargas.LocalCases.SecondEquation

/-!
# Actual ramification-one occurrence profiles at a divalent wall

Source: Draisma--Vargas Part I, Case {w2-r1}, Figures 37--38.  The source's
refinement equation is
`k₁ + k₂ = |A₀| = k₃`; when the first occurrence dangles, dangling-no-glue
gives `k₁ = 1` and hence `k₃ = k₂ + 1`.

The input is `SecondEquation.W2SourceInput` and an actual wall
block of local ramification one.  No extra no-return or classification
hypothesis is needed here: its three incident occurrences occupy both actual
target directions, so their fibre counts are two and one.  The singleton
direction's occurrence has index `|A₀| ≥ 2`, and therefore cannot dangle.
The input's surviving-valency trichotomy then leaves precisely the nd2 and
nd3 profiles.  All witnesses below retain literal source-edge occurrences.

This module does not assert exhaustion of the ramification-two branch or
construct the outgoing stable-path census needed by Equation (10).
-/

namespace DraismaVargas.LocalCases.W2R1SourceProfile

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-- Balancing separately over a single actual target-edge occurrence. -/
theorem sum_sourceEdgeIndex_target
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (targetEdge : target.edges)
    (hIncident : targetEdge ∈ GluingDatum.incidentEdges vertex.1.1) :
    (∑ edge : IncidentSourceEdge data vertex,
      if edge.1.1.1 = targetEdge then (data.sourceEdgeIndex edge.1 : ℤ) else 0) =
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
  classical
  calc
    (∑ edge : IncidentSourceEdge data vertex,
        if edge.1.1.1 = targetEdge then (data.sourceEdgeIndex edge.1 : ℤ) else 0) =
        ∑ item : Σ edge : {edge : target.edges //
            edge ∈ GluingDatum.incidentEdges vertex.1.1},
          {block : (data.edgePartition edge.1).Blocks //
            block ∈ SheetPartition.blocksWithin (data.edgePartition edge.1)
              (data.vertexPartition vertex.1.1) ⟨vertex.1.2, vertex.2⟩},
          if item.1.1 = targetEdge then
            ((data.edgePartition item.1.1).blockCard item.2.1.1 : ℤ) else 0 :=
      Fintype.sum_equiv (incidentSourceEdgeEquiv data vertex) _ _ fun _ ↦ rfl
    _ = ∑ edge : {edge : target.edges //
          edge ∈ GluingDatum.incidentEdges vertex.1.1},
        if edge.1 = targetEdge then
          ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0 := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun edge _ ↦ ?_
      by_cases hEdge : edge.1 = targetEdge
      · simp only [if_pos hEdge]
        exact (Finset.sum_coe_sort
          (SheetPartition.blocksWithin (data.edgePartition edge.1)
            (data.vertexPartition vertex.1.1) ⟨vertex.1.2, vertex.2⟩)
          (fun block ↦ ((data.edgePartition edge.1).blockCard block.1 : ℤ))).trans
          (sum_blockCard_blocksWithin _ _
            (refines_of_mem_incidentEdges data edge.2) ⟨vertex.1.2, vertex.2⟩)
      · simp only [if_neg hEdge, Finset.sum_const_zero]
    _ = ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
      rw [Fintype.sum_eq_single ⟨targetEdge, hIncident⟩]
      · simp
      · intro edge hNe
        have hValue : edge.1 ≠ targetEdge := fun h ↦ hNe (Subtype.ext h)
        simp only [hValue, if_false]

/-- The incident source occurrences over one of the two named directions. -/
noncomputable def fibre (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) (label : Fin 2) :
    Finset (IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :=
  Finset.univ.filter fun edge ↦ edge.1.1.1 = star.edge label

namespace fibre

variable (data : GluingDatum target degree) (star : TwoStar target wall)
  (block : WallBlock data wall)

@[simp] theorem mem (label : Fin 2)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    edge ∈ fibre data star block label ↔ edge.1.1.1 = star.edge label := by
  simp [fibre]

theorem sum_index (label : Fin 2) :
    (∑ edge ∈ fibre data star block label, (data.sourceEdgeIndex edge.1 : ℤ)) =
      ((data.vertexPartition wall).blockCard block.1 : ℤ) := by
  rw [fibre, Finset.sum_filter]
  simpa only [WallBlock.sourceVertex, GluingDatum.sourceEndpoint, block.2] using
    sum_sourceEdgeIndex_target data (WallBlock.sourceVertex data wall block)
      (star.edge label) (star.edge_mem_incidentEdges label)

theorem nonempty (label : Fin 2) : (fibre data star block label).Nonempty := by
  classical
  by_contra hEmpty
  have hEmpty' := Finset.not_nonempty_iff_eq_empty.mp hEmpty
  have hSum := sum_index data star block label
  rw [hEmpty', Finset.sum_empty] at hSum
  have hPos := (data.vertexPartition wall).blockCard_pos block.1
  omega

theorem union : fibre data star block 0 ∪ fibre data star block 1 = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro edge
  have hIncident := (incident_iff_target_mem_and_rel data edge.1 _).mp edge.2 |>.1
  let label := star.label.symm ⟨edge.1.1.1, hIncident⟩
  have hTarget : star.edge label = edge.1.1.1 :=
    congrArg Subtype.val (star.label.apply_symm_apply ⟨edge.1.1.1, hIncident⟩)
  have hLabel : label = 0 ∨ label = 1 := by omega
  rcases hLabel with hZero | hOne
  · apply Finset.mem_union_left
    exact (mem data star block 0 edge).mpr (hZero ▸ hTarget.symm)
  · apply Finset.mem_union_right
    exact (mem data star block 1 edge).mpr (hOne ▸ hTarget.symm)

theorem disjoint : Disjoint (fibre data star block 0) (fibre data star block 1) := by
  classical
  apply Finset.disjoint_left.mpr
  intro edge hZero hOne
  have hEq := ((mem data star block 0 edge).mp hZero).symm.trans
    ((mem data star block 1 edge).mp hOne)
  have := star.edge_injective hEq
  omega

theorem card_add_eq_three
    (hR : data.localRamification wall block = 1) :
    (fibre data star block 0).card + (fibre data star block 1).card = 3 := by
  have hCard := W2SourceInput.card_incidentSourceEdge_wallBlock (data := data) star block
  rw [hR] at hCard
  have hUnion := Finset.card_union_of_disjoint (disjoint data star block)
  rw [union data star block, Finset.card_univ] at hUnion
  omega

end fibre

/-- The literal `2+1` incidence profile of a ramification-one wall block.
The direction labels belong to the supplied two-star; only their order is
chosen.  Completeness concerns source occurrences, not their endpoints. -/
structure OccurrenceProfile (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall) where
  doubleLabel : Fin 2
  singleLabel : Fin 2
  labels_ne : doubleLabel ≠ singleLabel
  first : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  second : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  third : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  first_ne_second : first ≠ second
  first_target : first.1.1.1 = star.edge doubleLabel
  second_target : second.1.1.1 = star.edge doubleLabel
  third_target : third.1.1.1 = star.edge singleLabel
  exhaustive : ∀ edge, edge = first ∨ edge = second ∨ edge = third
  pair_index : data.sourceEdgeIndex first.1 + data.sourceEdgeIndex second.1 =
    (data.vertexPartition wall).blockCard block.1
  single_index : data.sourceEdgeIndex third.1 =
    (data.vertexPartition wall).blockCard block.1

/-- Refinement and ramification one force the actual two-plus-one profile.
This step does not need validity or a dangling hypothesis. -/
theorem exists_occurrenceProfile (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 1) :
    Nonempty (OccurrenceProfile data star block) := by
  classical
  have hCount := fibre.card_add_eq_three data star block hR
  have hZeroPos := Finset.card_pos.mpr (fibre.nonempty data star block 0)
  have hOnePos := Finset.card_pos.mpr (fibre.nonempty data star block 1)
  have hShape : ∃ doubleLabel singleLabel : Fin 2, doubleLabel ≠ singleLabel ∧
      (fibre data star block doubleLabel).card = 2 ∧
      (fibre data star block singleLabel).card = 1 := by
    by_cases hZero : (fibre data star block 0).card = 2
    · exact ⟨0, 1, by decide, hZero, by omega⟩
    · exact ⟨1, 0, by decide, by omega, by omega⟩
  obtain ⟨doubleLabel, singleLabel, hLabels, hDouble, hSingle⟩ := hShape
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hDouble
  obtain ⟨third, hThird⟩ := Finset.card_eq_one.mp hSingle
  have hUnion : fibre data star block doubleLabel ∪ fibre data star block singleLabel =
      Finset.univ := by
    fin_cases doubleLabel <;> fin_cases singleLabel
    · exact (hLabels rfl).elim
    · exact fibre.union data star block
    · rw [Finset.union_comm]
      exact fibre.union data star block
    · exact (hLabels rfl).elim
  have hFirstMem : first ∈ fibre data star block doubleLabel := by simp [hPair]
  have hSecondMem : second ∈ fibre data star block doubleLabel := by simp [hPair]
  have hThirdMem : third ∈ fibre data star block singleLabel := by simp [hThird]
  have hPairSum := fibre.sum_index data star block doubleLabel
  rw [hPair, Finset.sum_pair hNe] at hPairSum
  have hThirdSum := fibre.sum_index data star block singleLabel
  rw [hThird, Finset.sum_singleton] at hThirdSum
  refine ⟨{
    doubleLabel := doubleLabel
    singleLabel := singleLabel
    labels_ne := hLabels
    first := first
    second := second
    third := third
    first_ne_second := hNe
    first_target := (fibre.mem data star block doubleLabel first).mp hFirstMem
    second_target := (fibre.mem data star block doubleLabel second).mp hSecondMem
    third_target := (fibre.mem data star block singleLabel third).mp hThirdMem
    exhaustive := ?_
    pair_index := by exact_mod_cast hPairSum
    single_index := by exact_mod_cast hThirdSum }⟩
  intro edge
  have hMember : edge ∈ fibre data star block doubleLabel ∪
      fibre data star block singleLabel := by rw [hUnion]; exact Finset.mem_univ _
  simpa only [hPair, hThird, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, or_assoc] using hMember

namespace OccurrenceProfile

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}

theorem first_ne_third (profile : OccurrenceProfile data star block) :
    profile.first ≠ profile.third := by
  intro hEq
  have hTarget := profile.first_target.symm.trans
    ((congrArg (fun edge ↦ edge.1.1.1) hEq).trans profile.third_target)
  exact profile.labels_ne (star.edge_injective hTarget)

theorem second_ne_third (profile : OccurrenceProfile data star block) :
    profile.second ≠ profile.third := by
  intro hEq
  have hTarget := profile.second_target.symm.trans
    ((congrArg (fun edge ↦ edge.1.1.1) hEq).trans profile.third_target)
  exact profile.labels_ne (star.edge_injective hTarget)

theorem incident_univ (profile : OccurrenceProfile data star block) :
    (Finset.univ : Finset (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block))) =
        {profile.first, profile.second, profile.third} := by
  ext edge
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact profile.exhaustive edge

/-- Relabel the two occurrences over the doubled direction. -/
def swap (profile : OccurrenceProfile data star block) :
    OccurrenceProfile data star block where
  doubleLabel := profile.doubleLabel
  singleLabel := profile.singleLabel
  labels_ne := profile.labels_ne
  first := profile.second
  second := profile.first
  third := profile.third
  first_ne_second := profile.first_ne_second.symm
  first_target := profile.second_target
  second_target := profile.first_target
  third_target := profile.third_target
  exhaustive edge := by
    rcases profile.exhaustive edge with hFirst | hSecond | hThird
    · exact Or.inr (Or.inl hFirst)
    · exact Or.inl hSecond
    · exact Or.inr (Or.inr hThird)
  pair_index := by rw [Nat.add_comm]; exact profile.pair_index
  single_index := profile.single_index

/-- The singleton direction has index at least two, since the other direction
contains two positive occurrences. -/
theorem two_le_third_index (profile : OccurrenceProfile data star block) :
    2 ≤ data.sourceEdgeIndex profile.third.1 := by
  have hFirst := sourceEdgeIndex_pos data profile.first.1
  have hSecond := sourceEdgeIndex_pos data profile.second.1
  have hPair := profile.pair_index
  have hThird := profile.single_index
  omega

/-- The singleton-side occurrence cannot dangle. Together with the exclusion
of surviving valency one, this will force survivors in both directions. -/
theorem third_not_isDangling (profile : OccurrenceProfile data star block)
    (hNoGlue : DanglingEdgeNoGlue data) : ¬ IsDangling data profile.third.1 := by
  intro hDangling
  have hOne := hNoGlue profile.third.1 hDangling
  have hTwo := profile.two_le_third_index
  omega

theorem nonDanglingValency_eq_three (profile : OccurrenceProfile data star block)
    (hFirst : ¬ IsDangling data profile.first.1)
    (hSecond : ¬ IsDangling data profile.second.1)
    (hThird : ¬ IsDangling data profile.third.1) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3 := by
  classical
  rw [← card_filter_not_isDangling_eq_nonDanglingValency, profile.incident_univ]
  rw [Finset.filter_insert, if_pos hFirst, Finset.filter_insert, if_pos hSecond,
    Finset.filter_singleton, if_pos hThird]
  have hNot : profile.first ∉ ({profile.second, profile.third} : Finset
      (IncidentSourceEdge data (WallBlock.sourceVertex data wall block))) := by
    intro hMem
    rcases Finset.mem_insert.mp hMem with hSecond | hThird
    · exact profile.first_ne_second hSecond
    · exact profile.first_ne_third (Finset.mem_singleton.mp hThird)
  rw [Finset.card_insert_of_notMem hNot, Finset.card_pair profile.second_ne_third]

theorem nonDanglingValency_eq_two (profile : OccurrenceProfile data star block)
    (hFirst : IsDangling data profile.first.1)
    (hSecond : ¬ IsDangling data profile.second.1)
    (hThird : ¬ IsDangling data profile.third.1) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2 := by
  classical
  rw [← card_filter_not_isDangling_eq_nonDanglingValency, profile.incident_univ]
  rw [Finset.filter_insert, if_neg (not_not_intro hFirst), Finset.filter_insert,
    if_pos hSecond, Finset.filter_singleton, if_pos hThird]
  exact Finset.card_pair profile.second_ne_third

/-- Both doubled-side occurrences cannot dangle: that would leave surviving
valency one, excluded by the source input. -/
theorem not_both_isDangling (profile : OccurrenceProfile data star block)
    (input : W2SourceInput data star)
    (hFirst : IsDangling data profile.first.1)
    (hSecond : IsDangling data profile.second.1) : False := by
  classical
  have hThird := profile.third_not_isDangling input.dangling_no_glue
  have hValency : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 1 := by
    rw [← card_filter_not_isDangling_eq_nonDanglingValency, profile.incident_univ]
    rw [Finset.filter_insert, if_neg (not_not_intro hFirst), Finset.filter_insert,
      if_neg (not_not_intro hSecond), Finset.filter_singleton, if_pos hThird]
    exact Finset.card_singleton _
  have hCases := input.nonDangling_valency block
  omega

end OccurrenceProfile

/-- The two actual source profiles in Figures 37--38, normalized so the
possible dangling occurrence is first.  In both cases the second and third
occurrences survive over different target directions. -/
structure SourceProfile (data : GluingDatum target degree)
    (star : TwoStar target wall) (block : WallBlock data wall)
    extends OccurrenceProfile data star block where
  ramification : data.localRamification wall block = 1
  second_survives : ¬ IsDangling data second.1
  third_survives : ¬ IsDangling data third.1
  cases :
    (nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3 ∧
      ¬ IsDangling data first.1) ∨
    (nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2 ∧
      IsDangling data first.1 ∧ data.sourceEdgeIndex first.1 = 1 ∧
      data.sourceEdgeIndex third.1 = data.sourceEdgeIndex second.1 + 1)

/-- Every actual ramification-one block of the divalent source input
has one of the paper's two occurrence profiles, with no added local premise. -/
theorem exists_sourceProfile {data : GluingDatum target degree}
    {star : TwoStar target wall} (input : W2SourceInput data star)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 1) :
    Nonempty (SourceProfile data star block) := by
  classical
  obtain ⟨profile⟩ := exists_occurrenceProfile data star block hR
  have hThird := profile.third_not_isDangling input.dangling_no_glue
  have hBuild : ∀ profile : OccurrenceProfile data star block,
      IsDangling data profile.first.1 → ¬ IsDangling data profile.second.1 →
      Nonempty (SourceProfile data star block) := by
    intro profile hFirst hSecond
    have hThird := profile.third_not_isDangling input.dangling_no_glue
    have hOne := input.dangling_no_glue profile.first.1 hFirst
    refine ⟨{
      toOccurrenceProfile := profile
      ramification := hR
      second_survives := hSecond
      third_survives := hThird
      cases := Or.inr ⟨profile.nonDanglingValency_eq_two hFirst hSecond hThird,
        hFirst, hOne, ?_⟩ }⟩
    have hPair := profile.pair_index
    have hSingle := profile.single_index
    omega
  by_cases hFirst : IsDangling data profile.first.1
  · exact hBuild profile hFirst (profile.not_both_isDangling input hFirst)
  · by_cases hSecond : IsDangling data profile.second.1
    · exact hBuild profile.swap hSecond hFirst
    · exact ⟨{
        toOccurrenceProfile := profile
        ramification := hR
        second_survives := hSecond
        third_survives := hThird
        cases := Or.inl ⟨profile.nonDanglingValency_eq_three hFirst hSecond hThird,
          hFirst⟩ }⟩

namespace SourceProfile

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}

/-- Figure 38's two surviving occurrences lie on the same actual stable
path, not merely rows assigned to an arbitrary presentation. -/
theorem nd2_stablePath_eq (profile : SourceProfile data star block)
    (hNd2 : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2) :
    NonDanglingEdge.stablePath (⟨profile.second.1, profile.second_survives⟩ : NonDanglingEdge data) =
      NonDanglingEdge.stablePath (⟨profile.third.1, profile.third_survives⟩ : NonDanglingEdge data) := by
  apply stablePath_eq_of_consecutive
  refine ⟨?_, WallBlock.sourceVertex data wall block, profile.second.2,
    profile.third.2, hNd2⟩
  intro hEq
  apply profile.toOccurrenceProfile.second_ne_third
  have hValue : profile.second.1 = profile.third.1 :=
    congrArg (fun edge : NonDanglingEdge data ↦ edge.1) hEq
  exact Subtype.ext hValue

end SourceProfile

/-- Refine the ramification split into two actual source profiles.
The alternative is precisely ramification two; no nd3 claim is made
about that branch here. -/
theorem sourceProfiles_or_concentrated {data : GluingDatum target degree}
    {star : TwoStar target wall} (input : W2SourceInput data star) :
    (∃ first second : WallBlock data wall, first ≠ second ∧
      Nonempty (SourceProfile data star first) ∧
        Nonempty (SourceProfile data star second)) ∨
    ∃ block : WallBlock data wall, data.localRamification wall block = 2 := by
  rcases input.ramification_split_or_concentrated with hSplit | hConcentrated
  · obtain ⟨first, second, hNe, hFirst, hSecond⟩ := hSplit
    exact Or.inl ⟨first, second, hNe, exists_sourceProfile input first hFirst,
      exists_sourceProfile input second hSecond⟩
  · exact Or.inr hConcentrated

end DraismaVargas.LocalCases.W2R1SourceProfile
