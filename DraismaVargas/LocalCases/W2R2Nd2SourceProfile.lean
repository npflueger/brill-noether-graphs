module

public import DraismaVargas.LocalCases.W2R2SourceProfile
public import DraismaVargas.LocalCases.W3R1SourceProfile

@[expose] public section

/-!
# The actual index profiles of the two excluded nd2 cases of Case {w2-r2}

Source: Draisma--Vargas Part I, Case {w2-r2-nd2} (Cardinalities M and P),
Figure 36. This file
identifies the two surviving occurrences and proves their indices are either
`k,k` with local degree `k+1`, or `k,k+2` with local degree `k+2`.
The two occurrences lie on one actual stable path.

These are profiles, not exclusions. In particular, their target directions
are not assumed distinct: harmonicity alone leaves a degree-two, unit-index
same-direction exception. The source uses inherited no-return/full-rank data
to exclude inappropriate configurations; those are not fields of W2SourceInput.
No matrix compatibility or nonsingular incoming resolution is asserted here.
-/

namespace DraismaVargas.LocalCases.W2R2Nd2SourceProfile

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open W3R1SourceProfile

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-- The source's non-dangling ramification formula with `r=nd=2`. -/
theorem sum_survivor_index {data : GluingDatum target degree}
    (hNoGlue : DanglingEdgeNoGlue data) (block : WallBlock data wall)
    (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2) :
    (∑ edge ∈ survivors data block, (data.sourceEdgeIndex edge.1 : ℤ)) =
      2 * ((data.vertexPartition wall).blockCard block.1 : ℤ) - 2 := by
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
  rw [hRam, hR, hNd, hCard] at hForm
  change _ = _ - 2 + 2 * _ - ∑ edge ∈ survivors data block, _ at hForm
  omega

/-- The actual surviving pair, sorted by dilation index. -/
structure SourceProfile (data : GluingDatum target degree)
    (block : WallBlock data wall) where
  small : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  large : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)
  distinct : small ≠ large
  surviving : survivors data block = {small, large}
  cases :
    (data.sourceEdgeIndex small.1 = data.sourceEdgeIndex large.1 ∧
      data.sourceEdgeIndex small.1 + 1 = (data.vertexPartition wall).blockCard block.1) ∨
    (data.sourceEdgeIndex small.1 + 2 = data.sourceEdgeIndex large.1 ∧
      data.sourceEdgeIndex large.1 = (data.vertexPartition wall).blockCard block.1)

theorem exists_sourceProfile {data : GluingDatum target degree}
    {star : TwoStar target wall} (input : W2SourceInput data star)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 2)
    (hNd : nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2) :
    Nonempty (SourceProfile data block) := by
  classical
  have hCard : (survivors data block).card = 2 := by rw [card_survivors, hNd]
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hCard
  have hSum := sum_survivor_index input.dangling_no_glue block hR hNd
  rw [hPair, Finset.sum_pair hNe] at hSum
  have hFirstLe := sourceEdgeIndex_le_blockCard data
    (WallBlock.sourceVertex data wall block) first
  have hSecondLe := sourceEdgeIndex_le_blockCard data
    (WallBlock.sourceVertex data wall block) second
  have hBlock : (data.vertexPartition (WallBlock.sourceVertex data wall block).1.1).blockCard
      (WallBlock.sourceVertex data wall block).1.2 =
        (data.vertexPartition wall).blockCard block.1 :=
    congrArg (data.vertexPartition wall).blockCard block.2
  rw [hBlock] at hFirstLe hSecondLe
  by_cases hOrder : data.sourceEdgeIndex first.1 ≤ data.sourceEdgeIndex second.1
  · exact ⟨⟨first, second, hNe, hPair, by omega⟩⟩
  · exact ⟨⟨second, first, hNe.symm, hPair.trans (Finset.pair_comm _ _), by omega⟩⟩

namespace SourceProfile

variable {data : GluingDatum target degree} {block : WallBlock data wall}

theorem small_survives (profile : SourceProfile data block) :
    ¬ IsDangling data profile.small.1 := by
  apply (mem_survivors data block _).mp
  rw [profile.surviving]
  exact Finset.mem_insert_self _ _

theorem large_survives (profile : SourceProfile data block) :
    ¬ IsDangling data profile.large.1 := by
  apply (mem_survivors data block _).mp
  rw [profile.surviving]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem valency (profile : SourceProfile data block) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2 := by
  rw [← card_survivors, profile.surviving, Finset.card_pair profile.distinct]

/-- The single stable-row label `h` in Figure 36 is an actual quotient class. -/
theorem stablePath_eq (profile : SourceProfile data block) :
    NonDanglingEdge.stablePath (⟨profile.small.1, profile.small_survives⟩ : NonDanglingEdge data) =
      NonDanglingEdge.stablePath (⟨profile.large.1, profile.large_survives⟩ : NonDanglingEdge data) := by
  apply stablePath_eq_of_consecutive
  refine ⟨?_, WallBlock.sourceVertex data wall block, profile.small.2,
    profile.large.2, profile.valency⟩
  intro hEq
  exact profile.distinct (Subtype.ext (congrArg (fun edge : NonDanglingEdge data ↦ edge.1) hEq))

/-- If the surviving pair has the same direction, only the smallest equal
index case can remain. This exposes, rather than assumes away, the no-return
issue left open by the weak wall input of Case {w2}. -/
theorem same_target_exception (profile : SourceProfile data block)
    (hTarget : profile.small.1.1.1 = profile.large.1.1.1) :
    (data.vertexPartition wall).blockCard block.1 = 2 ∧
      data.sourceEdgeIndex profile.small.1 = 1 ∧ data.sourceEdgeIndex profile.large.1 = 1 := by
  have hIncident := (incident_iff_target_mem_and_rel data profile.small.1 _).mp profile.small.2 |>.1
  have hLe := sum_index_le_of_same_target data
    (WallBlock.sourceVertex data wall block) {profile.small, profile.large}
    profile.small.1.1.1 hIncident (by
      intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with rfl | hLarge
      · rfl
      · exact (Finset.mem_singleton.mp hLarge) ▸ hTarget.symm)
  rw [Finset.sum_pair profile.distinct] at hLe
  have hBlock : (data.vertexPartition (WallBlock.sourceVertex data wall block).1.1).blockCard
      (WallBlock.sourceVertex data wall block).1.2 =
        (data.vertexPartition wall).blockCard block.1 :=
    congrArg (data.vertexPartition wall).blockCard block.2
  rw [hBlock] at hLe
  have hSmallPos := sourceEdgeIndex_pos data profile.small.1
  have hLargePos := sourceEdgeIndex_pos data profile.large.1
  rcases profile.cases with ⟨hEq, hSize⟩ | ⟨hGap, hSize⟩ <;> omega

/-- The unequal-index P profile necessarily has distinct target directions. -/
theorem target_ne_of_indices_ne (profile : SourceProfile data block)
    (hNe : data.sourceEdgeIndex profile.small.1 ≠ data.sourceEdgeIndex profile.large.1) :
    profile.small.1.1.1 ≠ profile.large.1.1.1 := by
  intro hTarget
  obtain ⟨_, hSmall, hLarge⟩ := profile.same_target_exception hTarget
  exact hNe (hSmall.trans hLarge.symm)

end SourceProfile

end DraismaVargas.LocalCases.W2R2Nd2SourceProfile
