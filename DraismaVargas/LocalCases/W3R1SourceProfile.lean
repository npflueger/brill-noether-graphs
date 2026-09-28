import DraismaVargas.LocalCases.ThirdEquation
import DraismaVargas.LocalCases.W2R1SourceProfile

/-!
# Actual ramification-one profiles at a trivalent wall

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w3-r1}` and its nd2 sub-case
(Figure 31). We apply the paper's non-dangling ramification formula to literal
incident occurrences. This excludes the nd0 branch and recovers the nd2 indices
and their distinct target directions, without assuming an additional no-return
receipt. Outgoing resolutions and inherited stable rows are treated in other
modules.
-/

namespace DraismaVargas.LocalCases.W3R1SourceProfile

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency ThirdEquation

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-- All surviving occurrences incident to the actual wall block. -/
noncomputable def survivors (data : GluingDatum target degree)
    (block : WallBlock data wall) :
    Finset (IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :=
  Finset.univ.filter fun edge ↦ ¬ IsDangling data edge.1

@[simp] theorem mem_survivors (data : GluingDatum target degree)
    (block : WallBlock data wall)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    edge ∈ survivors data block ↔ ¬ IsDangling data edge.1 := by
  simp [survivors]

theorem card_survivors (data : GluingDatum target degree) (block : WallBlock data wall) :
    (survivors data block).card =
      nonDanglingValency data (WallBlock.sourceVertex data wall block) :=
  card_filter_not_isDangling_eq_nonDanglingValency data _

/-- The source's `nd. r` formula, with the ramification-one value inserted. -/
theorem sum_survivor_index {data : GluingDatum target degree}
    (hNoGlue : DanglingEdgeNoGlue data) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 1) :
    (∑ edge ∈ survivors data block, (data.sourceEdgeIndex edge.1 : ℤ)) =
      (nonDanglingValency data (WallBlock.sourceVertex data wall block) : ℤ) +
        2 * ((data.vertexPartition wall).blockCard block.1 : ℤ) - 3 := by
  have hForm := localRamification_eq_nonDangling_form data hNoGlue
    (WallBlock.sourceVertex data wall block)
  have hRam : data.localRamification
      (WallBlock.sourceVertex data wall block).1.1
      ⟨(WallBlock.sourceVertex data wall block).1.2,
        (WallBlock.sourceVertex data wall block).2⟩ =
        data.localRamification wall block :=
    congrArg (data.localRamification wall) (Subtype.ext block.2)
  have hCard : (data.vertexPartition
      (WallBlock.sourceVertex data wall block).1.1).blockCard
        (WallBlock.sourceVertex data wall block).1.2 =
        (data.vertexPartition wall).blockCard block.1 :=
    congrArg (data.vertexPartition wall).blockCard block.2
  rw [hRam, hR, hCard] at hForm
  change _ = _ - 2 + 2 * _ - ∑ edge ∈ survivors data block, _ at hForm
  linarith

/-- Ramification one cannot lie at an isolated pruned vertex: it would force
the impossible integer equality `2 |A| = 3`. -/
theorem nonDanglingValency_ne_zero {data : GluingDatum target degree}
    (hNoGlue : DanglingEdgeNoGlue data) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 1) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) ≠ 0 := by
  intro hZero
  have hEmpty : survivors data block = ∅ := by
    rw [← Finset.card_eq_zero, card_survivors, hZero]
  have hSum := sum_survivor_index hNoGlue block hR
  rw [hEmpty, Finset.sum_empty, hZero] at hSum
  omega

/-- The nd0 branch of the W3 router is impossible. -/
theorem valency_eq_two_or_three {data : GluingDatum target degree}
    {star : ThreeStar target wall} (input : W3SourceInput data star)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 1) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2 ∨
      nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3 := by
  rcases input.nonDangling_valency block with hZero | hTwo | hThree
  · exact (nonDanglingValency_ne_zero input.dangling_no_glue block hR hZero).elim
  · exact Or.inl hTwo
  · exact Or.inr hThree

/-- A singleton at a trivalent target cannot have ramification one: three
units of total directional degree cannot fill four positive occurrences. -/
theorem two_le_blockCard (data : GluingDatum target degree)
    (star : ThreeStar target wall) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 1) :
    2 ≤ (data.vertexPartition wall).blockCard block.1 := by
  have hCard := W3SourceInput.card_incidentSourceEdge_wallBlock (data := data) star block
  rw [hR] at hCard
  have hSum := sum_sourceEdgeIndex_incident data (WallBlock.sourceVertex data wall block)
  have hLe : (Fintype.card (IncidentSourceEdge data
      (WallBlock.sourceVertex data wall block)) : ℤ) ≤
      ∑ edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block),
        (data.sourceEdgeIndex edge.1 : ℤ) := by
    calc
      _ = ∑ _edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block),
          (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun edge _ ↦ by
        exact_mod_cast sourceEdgeIndex_pos data edge.1
  have hTarget : (GluingDatum.incidentEdges
      (WallBlock.sourceVertex data wall block).1.1).card = 3 := star.card_incidentEdges
  have hBlock : (data.vertexPartition (WallBlock.sourceVertex data wall block).1.1).blockCard
      (WallBlock.sourceVertex data wall block).1.2 =
        (data.vertexPartition wall).blockCard block.1 :=
    congrArg (data.vertexPartition wall).blockCard block.2
  rw [hTarget, hBlock] at hSum
  omega

/-- Any set of distinct occurrences in one actual target direction has total
index at most the local degree. This is harmonicity, not no-return. -/
theorem sum_index_le_of_same_target (data : GluingDatum target degree)
    (vertex : data.SourceVertex) (edges : Finset (IncidentSourceEdge data vertex))
    (targetEdge : target.edges)
    (hIncident : targetEdge ∈ GluingDatum.incidentEdges vertex.1.1)
    (hTarget : ∀ edge ∈ edges, edge.1.1.1 = targetEdge) :
    (∑ edge ∈ edges, (data.sourceEdgeIndex edge.1 : ℤ)) ≤
      ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) := by
  classical
  calc
    _ = ∑ edge ∈ edges,
        if edge.1.1.1 = targetEdge then (data.sourceEdgeIndex edge.1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro edge hEdge
      rw [if_pos (hTarget edge hEdge)]
    _ ≤ ∑ edge : IncidentSourceEdge data vertex,
        if edge.1.1.1 = targetEdge then (data.sourceEdgeIndex edge.1 : ℤ) else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ by split_ifs <;> positivity)
    _ = _ := W2R1SourceProfile.sum_sourceEdgeIndex_target data vertex targetEdge hIncident

/-- Figure 31 on literal source occurrences, ordered by increasing index. -/
structure Nd2Profile (data : GluingDatum target degree)
    (block : WallBlock data wall) where
  small : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  large : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  distinct : small ≠ large
  surviving : survivors data block = {small, large}
  target_ne : small.1.1.1 ≠ large.1.1.1
  small_index : data.sourceEdgeIndex small.1 + 1 =
    (data.vertexPartition wall).blockCard block.1
  large_index : data.sourceEdgeIndex large.1 =
    (data.vertexPartition wall).blockCard block.1

/-- Harmonicity and the paper's non-dangling formula give Figure 31 outright.
In particular no-return does not need to be assumed for this local profile. -/
theorem exists_nd2Profile {data : GluingDatum target degree}
    {star : ThreeStar target wall} (input : W3SourceInput data star)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 1)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2) :
    Nonempty (Nd2Profile data block) := by
  classical
  have hCard : (survivors data block).card = 2 := by rw [card_survivors, hNd]
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hCard
  have hSum := sum_survivor_index input.dangling_no_glue block hR
  rw [hNd, hPair, Finset.sum_pair hNe] at hSum
  have hFirstLe := sourceEdgeIndex_le_blockCard data
    (WallBlock.sourceVertex data wall block) first
  have hSecondLe := sourceEdgeIndex_le_blockCard data
    (WallBlock.sourceVertex data wall block) second
  have hBlock : (data.vertexPartition (WallBlock.sourceVertex data wall block).1.1).blockCard
      (WallBlock.sourceVertex data wall block).1.2 =
        (data.vertexPartition wall).blockCard block.1 :=
    congrArg (data.vertexPartition wall).blockCard block.2
  rw [hBlock] at hFirstLe hSecondLe
  have hSize := two_le_blockCard data star block hR
  have hTargets : first.1.1.1 ≠ second.1.1.1 := by
    intro hSame
    have hIncident := (incident_iff_target_mem_and_rel data first.1 _).mp first.2 |>.1
    have hLe := sum_index_le_of_same_target data
      (WallBlock.sourceVertex data wall block) {first, second}
      first.1.1.1 hIncident (by
        intro edge hEdge
        rcases Finset.mem_insert.mp hEdge with rfl | hSecond
        · rfl
        · exact (Finset.mem_singleton.mp hSecond) ▸ hSame.symm)
    rw [Finset.sum_pair hNe, hBlock] at hLe
    omega
  by_cases hOrder : data.sourceEdgeIndex first.1 ≤ data.sourceEdgeIndex second.1
  · exact ⟨⟨first, second, hNe, hPair, hTargets, by omega, by omega⟩⟩
  · exact ⟨⟨second, first, hNe.symm, hPair.trans (Finset.pair_comm _ _),
      hTargets.symm, by omega, by omega⟩⟩

namespace Nd2Profile

variable {data : GluingDatum target degree} {block : WallBlock data wall}

theorem small_survives (profile : Nd2Profile data block) :
    ¬ IsDangling data profile.small.1 := by
  apply (mem_survivors data block _).mp
  rw [profile.surviving]
  exact Finset.mem_insert_self _ _

theorem large_survives (profile : Nd2Profile data block) :
    ¬ IsDangling data profile.large.1 := by
  apply (mem_survivors data block _).mp
  rw [profile.surviving]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem valency (profile : Nd2Profile data block) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2 := by
  rw [← card_survivors, profile.surviving, Finset.card_pair profile.distinct]

/-- The two occurrences in Figure 31 lie in the same actual stable edge. -/
theorem stablePath_eq (profile : Nd2Profile data block) :
    NonDanglingEdge.stablePath (⟨profile.small.1, profile.small_survives⟩ : NonDanglingEdge data) =
      NonDanglingEdge.stablePath (⟨profile.large.1, profile.large_survives⟩ : NonDanglingEdge data) := by
  apply stablePath_eq_of_consecutive
  refine ⟨?_, WallBlock.sourceVertex data wall block, profile.small.2,
    profile.large.2, profile.valency⟩
  intro hEq
  apply profile.distinct
  exact Subtype.ext (congrArg (fun edge : NonDanglingEdge data ↦ edge.1) hEq)

end Nd2Profile

/-- The actual three survivors, with the source's largest-index convention.
The first two avoid the largest occurrence's target direction. They may have
the same target direction as each other, which is precisely case `t3`. -/
structure Nd3Profile (data : GluingDatum target degree)
    (block : WallBlock data wall) where
  first : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  second : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  largest : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  first_ne_second : first ≠ second
  first_ne_largest : first ≠ largest
  second_ne_largest : second ≠ largest
  surviving : survivors data block = {first, second, largest}
  first_le : data.sourceEdgeIndex first.1 ≤ data.sourceEdgeIndex largest.1
  second_le : data.sourceEdgeIndex second.1 ≤ data.sourceEdgeIndex largest.1
  first_target_ne : first.1.1.1 ≠ largest.1.1.1
  second_target_ne : second.1.1.1 ≠ largest.1.1.1
  index_sum : data.sourceEdgeIndex first.1 + data.sourceEdgeIndex second.1 +
    data.sourceEdgeIndex largest.1 = 2 * (data.vertexPartition wall).blockCard block.1

private theorem pair_index_le (data : GluingDatum target degree)
    (block : WallBlock data wall)
    (first second : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hNe : first ≠ second) (hTarget : first.1.1.1 = second.1.1.1) :
    data.sourceEdgeIndex first.1 + data.sourceEdgeIndex second.1 ≤
      (data.vertexPartition wall).blockCard block.1 := by
  have hIncident := (incident_iff_target_mem_and_rel data first.1 _).mp first.2 |>.1
  have hLe := sum_index_le_of_same_target data
    (WallBlock.sourceVertex data wall block) {first, second}
    first.1.1.1 hIncident (by
      intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with rfl | hSecond
      · rfl
      · exact (Finset.mem_singleton.mp hSecond) ▸ hTarget.symm)
  rw [Finset.sum_pair hNe] at hLe
  have hBlock : (data.vertexPartition (WallBlock.sourceVertex data wall block).1.1).blockCard
      (WallBlock.sourceVertex data wall block).1.2 =
        (data.vertexPartition wall).blockCard block.1 :=
    congrArg (data.vertexPartition wall).blockCard block.2
  rw [hBlock] at hLe
  exact_mod_cast hLe

/-- The source's largest-index argument proves the actual target-direction
normalization; no extra no-return assumption is used. -/
theorem exists_nd3Profile {data : GluingDatum target degree}
    {star : ThreeStar target wall} (input : W3SourceInput data star)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 1)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3) :
    Nonempty (Nd3Profile data block) := by
  classical
  have hCard : (survivors data block).card = 3 := by rw [card_survivors, hNd]
  obtain ⟨largest, hLargest, hMax⟩ := Finset.exists_max_image (survivors data block)
    (fun edge ↦ data.sourceEdgeIndex edge.1) (Finset.card_pos.mp (by omega))
  have hErase : ((survivors data block).erase largest).card = 2 := by
    rw [Finset.card_erase_of_mem hLargest, hCard]
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hErase
  have hFirst : first ∈ (survivors data block).erase largest := by simp [hPair]
  have hSecond : second ∈ (survivors data block).erase largest := by simp [hPair]
  have hFirstNe := (Finset.mem_erase.mp hFirst).1
  have hSecondNe := (Finset.mem_erase.mp hSecond).1
  have hFirstLe := hMax first (Finset.mem_of_mem_erase hFirst)
  have hSecondLe := hMax second (Finset.mem_of_mem_erase hSecond)
  have hTriple : survivors data block = {first, second, largest} := by
    rw [← Finset.insert_erase hLargest, hPair]
    rw [Finset.insert_comm largest first]
    exact congrArg (insert first) (Finset.pair_comm largest second)
  have hSum := sum_survivor_index input.dangling_no_glue block hR
  rw [hNd, hTriple, Finset.sum_insert (by simp [hNe, hFirstNe]),
    Finset.sum_pair hSecondNe] at hSum
  have hIndexSum : data.sourceEdgeIndex first.1 + data.sourceEdgeIndex second.1 +
      data.sourceEdgeIndex largest.1 = 2 * (data.vertexPartition wall).blockCard block.1 := by
    omega
  have hFirstPos := sourceEdgeIndex_pos data first.1
  have hSecondPos := sourceEdgeIndex_pos data second.1
  refine ⟨⟨first, second, largest, hNe, hFirstNe, hSecondNe, hTriple,
    hFirstLe, hSecondLe, ?_, ?_, hIndexSum⟩⟩
  · intro hTarget
    have hLe := pair_index_le data block first largest hFirstNe hTarget
    omega
  · intro hTarget
    have hLe := pair_index_le data block second largest hSecondNe hTarget
    omega

namespace Nd3Profile

variable {data : GluingDatum target degree} {block : WallBlock data wall}

theorem largest_index_le (profile : Nd3Profile data block) :
    data.sourceEdgeIndex profile.largest.1 ≤ (data.vertexPartition wall).blockCard block.1 := by
  have h := sourceEdgeIndex_le_blockCard data
    (WallBlock.sourceVertex data wall block) profile.largest
  simpa only [WallBlock.sourceVertex, GluingDatum.sourceEndpoint, block.2] using h

/-- The doubled-direction case `t3` in Figure 30. -/
theorem doubled_direction (profile : Nd3Profile data block)
    (hTarget : profile.first.1.1.1 = profile.second.1.1.1) :
    data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 =
        (data.vertexPartition wall).blockCard block.1 ∧
      data.sourceEdgeIndex profile.largest.1 =
        (data.vertexPartition wall).blockCard block.1 := by
  have hPair := pair_index_le data block profile.first profile.second
    profile.first_ne_second hTarget
  have hSum := profile.index_sum
  have hLargest := profile.largest_index_le
  omega

/-- The equality subcase of `t2` in Figure 28. -/
theorem indices_of_largest_eq (profile : Nd3Profile data block)
    (hEq : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard block.1) :
    data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 =
      (data.vertexPartition wall).blockCard block.1 := by
  have hSum := profile.index_sum
  omega

/-- In the strict subcase of `t2`, all three indices are at least two.
This is the source's reason that both ±1 shifts are legitimate (Figure 29). -/
theorem indices_two_le_of_largest_lt (profile : Nd3Profile data block)
    (hLt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard block.1) :
    2 ≤ data.sourceEdgeIndex profile.first.1 ∧
      2 ≤ data.sourceEdgeIndex profile.second.1 ∧
        2 ≤ data.sourceEdgeIndex profile.largest.1 := by
  have hSum := profile.index_sum
  have hFirst := profile.first_le
  have hSecond := profile.second_le
  omega

/-- Exhaustion of the three actual nd3 source profiles. Distinct directions
are literal target occurrences, not freely assigned labels. -/
theorem cases (profile : Nd3Profile data block) :
    (profile.first.1.1.1 = profile.second.1.1.1 ∧
      data.sourceEdgeIndex profile.largest.1 =
        (data.vertexPartition wall).blockCard block.1) ∨
    (profile.first.1.1.1 ≠ profile.second.1.1.1 ∧
      data.sourceEdgeIndex profile.largest.1 =
        (data.vertexPartition wall).blockCard block.1) ∨
    (profile.first.1.1.1 ≠ profile.second.1.1.1 ∧
      data.sourceEdgeIndex profile.largest.1 <
        (data.vertexPartition wall).blockCard block.1) := by
  by_cases hTarget : profile.first.1.1.1 = profile.second.1.1.1
  · exact Or.inl ⟨hTarget, (profile.doubled_direction hTarget).2⟩
  · rcases Nat.eq_or_lt_of_le profile.largest_index_le with hEq | hLt
    · exact Or.inr (Or.inl ⟨hTarget, hEq⟩)
    · exact Or.inr (Or.inr ⟨hTarget, hLt⟩)

end Nd3Profile

/-- Actual source-profile routing for the unique ramified W3 block. -/
theorem distinguished_sourceProfiles {data : GluingDatum target degree}
    {star : ThreeStar target wall} (input : W3SourceInput data star) :
    Nonempty (Nd2Profile data input.distinguishedBlock) ∨
      Nonempty (Nd3Profile data input.distinguishedBlock) := by
  rcases valency_eq_two_or_three input input.distinguishedBlock
    input.localRamification_distinguishedBlock with hTwo | hThree
  · exact Or.inl (exists_nd2Profile input _ input.localRamification_distinguishedBlock hTwo)
  · exact Or.inr (exists_nd3Profile input _ input.localRamification_distinguishedBlock hThree)

end DraismaVargas.LocalCases.W3R1SourceProfile
