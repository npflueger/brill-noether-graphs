import DraismaVargas.LocalCases.M11JoinedBranch
import DraismaVargas.LocalCases.StableGraphIncidence

/-!
# Joined M11 preserves selected-branch incidence multiplicities

The three old surviving flags are the profile's first, second, and third
occurrences. The joined branch flags are the first two retained occurrences
and the distinguished new occurrence. Their actual stable rows correspond
under `M11JoinedRowDescent.stablePathEquiv`.

`incidenceCount_of_three` counts flags by three indicator terms, not by the
cardinality of a set of stable rows. Thus rows may coincide, including the
two flags of a stable loop. The main theorem is only the selected-branch
incidence equality; other branch vertices and the global vertex equivalence
are treated elsewhere.
-/

namespace DraismaVargas.LocalCases.M11JoinedIncidence

open DraismaVargas.Infrastructure W4StableSource StablePathCount W4Assembly
open W2R1Target SecondEquation M11SourceCandidates M11JoinedBranch

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- The surviving-occurrence version of the three-flag indicator formula. -/
theorem incidenceCount_of_incidentEdges_three (vertex : data.SourceVertex)
    (first second third : NonDanglingEdge data)
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third) (hSecondThird : second ≠ third)
    (hStar : incidentEdges data vertex = {first, second, third})
    (path : StablePath data) :
    incidenceCount data vertex path =
      (if first.stablePath = path then 1 else 0) +
      (if second.stablePath = path then 1 else 0) +
      (if third.stablePath = path then 1 else 0) := by
  classical
  rw [incidenceCount, hStar]
  simp only [Finset.filter_insert, Finset.filter_singleton]
  split_ifs <;> simp_all

/-- A complete star of three distinct occurrences contributes three separate
row indicators. Their stable paths need not be distinct. -/
theorem incidenceCount_of_three (vertex : data.SourceVertex)
    (first second third : NonDanglingEdge data)
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third) (hSecondThird : second ≠ third)
    (hStar : nonDanglingIncident data vertex = {first.1, second.1, third.1})
    (path : StablePath data) :
    incidenceCount data vertex path =
      (if first.stablePath = path then 1 else 0) +
      (if second.stablePath = path then 1 else 0) +
      (if third.stablePath = path then 1 else 0) := by
  classical
  have hEdges : incidentEdges data vertex = {first, second, third} := by
    ext edge
    have hMem := Finset.ext_iff.mp hStar edge.1
    rw [mem_incidentEdges]
    simp only [mem_nonDanglingIncident, Finset.mem_insert, Finset.mem_singleton] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hIncident
      rcases hMem.mp ⟨edge.2, hIncident⟩ with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    · rintro (rfl | rfl | rfl)
      · exact (hMem.mpr (Or.inl rfl)).2
      · exact (hMem.mpr (Or.inr (Or.inl rfl))).2
      · exact (hMem.mpr (Or.inr (Or.inr rfl))).2
  exact incidenceCount_of_incidentEdges_three vertex first second third
    hFirstSecond hFirstThird hSecondThird hEdges path

/-- The profile exhausts the selected old star; the fourth flag is dangling. -/
theorem nonDanglingIncident_wallBlock {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    nonDanglingIncident data (WallBlock.sourceVertex data wall block) =
      {profile.first.1, profile.second.1, profile.third.1} := by
  classical
  ext edge
  rw [mem_nonDanglingIncident]
  constructor
  · rintro ⟨hSurvives, hIncident⟩
    rcases profile.exhaustive ⟨edge, hIncident⟩ with hFirst | hSecond | hThird | hDeleted
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (congrArg Subtype.val hFirst)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl (congrArg Subtype.val hSecond))
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (congrArg Subtype.val hThird))
    · have hEdge : edge = profile.deleted.edge.1 := congrArg Subtype.val hDeleted
      rw [hEdge] at hSurvives
      exact (hSurvives profile.deleted.dangling).elim
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl)
    · exact ⟨profile.first_survives, profile.first.2⟩
    · exact ⟨profile.second_survives, profile.second.2⟩
    · exact ⟨profile.third_survives, profile.third.2⟩

/-- The old selected star, counted without any row-distinctness assumption. -/
theorem incidenceCount_wallBlock {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (path : StablePath data) :
    incidenceCount data (WallBlock.sourceVertex data wall block) path =
      (if NonDanglingEdge.stablePath ⟨profile.first.1, profile.first_survives⟩ = path then 1 else 0) +
      (if NonDanglingEdge.stablePath ⟨profile.second.1, profile.second_survives⟩ = path then 1 else 0) +
      (if NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ = path then 1 else 0) := by
  classical
  let first : NonDanglingEdge data := ⟨profile.first.1, profile.first_survives⟩
  let second : NonDanglingEdge data := ⟨profile.second.1, profile.second_survives⟩
  let third : NonDanglingEdge data := ⟨profile.third.1, profile.third_survives⟩
  have hFirstSecond : first ≠ second := by
    intro h
    have hVal : profile.first.1 = profile.second.1 :=
      congrArg (fun edge : NonDanglingEdge data ↦ edge.1) h
    exact profile.first_ne_second (Subtype.ext hVal)
  have hFirstThird : first ≠ third := by
    intro h
    have hTarget := congrArg (fun edge : NonDanglingEdge data ↦ edge.1.1.1) h
    change profile.first.1.1.1 = profile.third.1.1.1 at hTarget
    rw [profile.first_target, profile.third_target] at hTarget
    exact profile.labels_ne (star.edge_injective hTarget)
  have hSecondThird : second ≠ third := by
    intro h
    have hTarget := congrArg (fun edge : NonDanglingEdge data ↦ edge.1.1.1) h
    change profile.second.1.1.1 = profile.third.1.1.1 at hTarget
    rw [profile.second_target, profile.third_target] at hTarget
    exact profile.labels_ne (star.edge_injective hTarget)
  exact incidenceCount_of_three _ first second third hFirstSecond hFirstThird hSecondThird
    (nonDanglingIncident_wallBlock profile) path

/-- The actual joined row equivalence preserves every selected-branch
incidence count, not just the three displayed row labels. -/
theorem incidenceCount_branchVertex (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (path : StablePath data) :
    incidenceCount data (WallBlock.sourceVertex data wall block) path =
      incidenceCount (joinedPattern data star block hCard).candidate.datum
        (branchVertex profile hCard)
        (M11JoinedRowDescent.stablePathEquiv input profile hCard path) := by
  classical
  have hNewFirstThird : firstEnd input profile hCard ≠ thirdEnd input profile hCard :=
    fun h ↦ oldEnd_ne_thirdEnd input profile hCard profile.first.1 (congrArg Subtype.val h)
  have hNewSecondThird : secondEnd input profile hCard ≠ thirdEnd input profile hCard :=
    fun h ↦ oldEnd_ne_thirdEnd input profile hCard profile.second.1 (congrArg Subtype.val h)
  rw [incidenceCount_wallBlock profile]
  rw [incidenceCount_of_three _ (firstEnd input profile hCard) (secondEnd input profile hCard)
    (thirdEnd input profile hCard) (firstEnd_ne_secondEnd input profile hCard)
    hNewFirstThird hNewSecondThird (nonDanglingIncident_branchVertex input profile hCard)]
  rw [firstEnd_stablePath, secondEnd_stablePath, thirdEnd_stablePath]
  simp only [Equiv.apply_eq_iff_eq]

end DraismaVargas.LocalCases.M11JoinedIncidence
