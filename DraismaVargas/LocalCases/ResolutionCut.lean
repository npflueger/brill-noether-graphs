module

public import DraismaVargas.LocalCases.BalancedGlobal
public import DraismaVargas.LocalCases.WallDegeneration

@[expose] public section

/-!
# Descending retained-edge cuts through a literal wall resolution

A separating cut whose crossing occurrence is retained cannot be crossed by
any new occurrence. The cut is therefore a union of complete source fibres,
and has a well-defined image in the old source. This is the occurrence-level
step needed to show that old surviving edges still survive in a resolution.
Genus of the induced side is a separate matter, not part of cut saturation.
-/

namespace DraismaVargas.LocalCases.ResolutionCut

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 W4StableSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

/-- Contract all newly inserted source occurrences of a literal candidate. -/
noncomputable def sourceMap (candidate : BalancedGlobal.Candidate target degree data wall) :
    candidate.datum.SourceVertex → data.SourceVertex :=
  GlobalResolution.sourceVertexMap data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
      candidate.contracts candidate.exterior)

theorem sourceMap_surjective (candidate : BalancedGlobal.Candidate target degree data wall) :
    Function.Surjective (sourceMap candidate) :=
  GlobalResolution.sourceVertexMap_surjective data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
      candidate.contracts candidate.exterior)
    (LocalResolution.paste_contracts _ _ _)

theorem sourceMap_oldSourceEdge_ends (candidate : BalancedGlobal.Candidate target degree data wall)
    (edge : data.SourceEdge) :
    (sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge edge)).1,
      sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge edge)).2) =
      data.sourceEnds edge :=
  GlobalResolution.sourceVertexMap_sourceEnds_oldSourceEdge data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
      candidate.contracts candidate.exterior)
    (LocalResolution.paste_contracts _ _ _) edge

theorem oldSourceEdge_injective (candidate : BalancedGlobal.Candidate target degree data wall) :
    Function.Injective candidate.oldSourceEdge := by
  intro first second hEq
  apply Subtype.ext
  apply Prod.ext
  · have hTarget := congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.1) hEq
    exact Option.some.inj ((occurrenceEquiv target wall candidate.right).injective hTarget)
  · exact congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.2) hEq

/-- No new occurrence can cross a cut whose unique crossing is a retained
old occurrence. Multiplicity one distinguishes the literal occurrences. -/
theorem new_endpoints_same_side
    (candidate : BalancedGlobal.Candidate target degree data wall)
    {left right : candidate.datum.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut candidate.datum.sourceGraph left right)
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left))
    (sheet : Fin degree) :
    candidate.datum.sourceEndpoint (oldVertex target wall) sheet ∈ cut.side ↔
      candidate.datum.sourceEndpoint (freshVertex target) sheet ∈ cut.side := by
  apply WallDegeneration.contractedStep_side_iff candidate.datum
    (contracted := occurrenceEquiv target wall candidate.right none) cut hEnds
  · intro hTarget
    have hLabels := (occurrenceEquiv target wall candidate.right).injective hTarget
    cases hLabels
  · refine ⟨candidate.newSourceEdge sheet, rfl, ?_, ?_⟩
    · exact congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall candidate.right
        (LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts)
        (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
          candidate.contracts candidate.exterior) sheet)
    · exact congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall candidate.right
        (LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts)
        (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
          candidate.contracts candidate.exterior) sheet)

/-- A retained-edge separating cut is saturated on every contraction fibre. -/
theorem cut_mem_iff_of_sourceMap_eq
    (candidate : BalancedGlobal.Candidate target degree data wall)
    {left right : candidate.datum.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut candidate.datum.sourceGraph left right)
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left))
    (first second : candidate.datum.SourceVertex)
    (hMap : sourceMap candidate first = sourceMap candidate second) :
    first ∈ cut.side ↔ second ∈ cut.side :=
  GlobalResolution.sourceVertex_mem_iff_of_sourceVertexMap_eq_of_new_edges data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
      candidate.contracts candidate.exterior)
    (LocalResolution.paste_contracts _ _ _) cut.side
    (new_endpoints_same_side candidate cut edge hEnds) first second hMap

/-- The literal image of a source-vertex side after contraction. -/
noncomputable def imageSide (candidate : BalancedGlobal.Candidate target degree data wall)
    (side : Finset candidate.datum.SourceVertex) : Finset data.SourceVertex := by
  classical
  exact side.image (sourceMap candidate)

/-- Saturation ensures membership in the image is exactly membership upstairs,
not just one implication. This handles every representative of a fibre. -/
theorem sourceMap_mem_imageSide_iff
    (candidate : BalancedGlobal.Candidate target degree data wall)
    {left right : candidate.datum.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut candidate.datum.sourceGraph left right)
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left))
    (vertex : candidate.datum.SourceVertex) :
    sourceMap candidate vertex ∈ imageSide candidate cut.side ↔ vertex ∈ cut.side := by
  classical
  constructor
  · intro hMem
    obtain ⟨other, hOther, hEq⟩ := Finset.mem_image.mp hMem
    exact (cut_mem_iff_of_sourceMap_eq candidate cut edge hEnds other vertex hEq).mp hOther
  · exact fun hMem ↦ Finset.mem_image.mpr ⟨vertex, hMem, rfl⟩

/-- A crossing occurrence is uniquely determined by an occurrence-safe cut,
not just by its unordered pair of endpoints. -/
theorem crossing_sourceEdge_eq (data : GluingDatum target degree)
    {left right : data.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut data.sourceGraph left right)
    (distinguished : data.SourceEdge)
    (hEnds : data.sourceEnds distinguished = (left, right) ∨
      data.sourceEnds distinguished = (right, left))
    (edge : data.SourceEdge)
    (hCross : ((data.sourceEnds edge).1 ∈ cut.side ∧ (data.sourceEnds edge).2 ∉ cut.side) ∨
      ((data.sourceEnds edge).2 ∈ cut.side ∧ (data.sourceEnds edge).1 ∉ cut.side)) :
    edge = distinguished := by
  apply WallDegeneration.sourceEdge_unique_of_num_edges_eq_one data cut.num_edges_endpoints _ hEnds
  rcases hCross with ⟨hFirst, hSecond⟩ | ⟨hSecond, hFirst⟩
  · have hPositive := num_edges_pos_of_sourceEnds data
      (Or.inl (show data.sourceEnds edge = ((data.sourceEnds edge).1, (data.sourceEnds edge).2) from rfl))
    have hCount := cut.cross_num_edges _ _ hFirst hSecond
    have hPair : (data.sourceEnds edge).1 = left ∧ (data.sourceEnds edge).2 = right := by
      by_contra hNot
      have hZero := hCount.trans (ite_eq_right hNot)
      omega
    exact Or.inl (Prod.ext hPair.1 hPair.2)
  · have hPositive := num_edges_pos_of_sourceEnds data
      (Or.inr (show data.sourceEnds edge = ((data.sourceEnds edge).1, (data.sourceEnds edge).2) from rfl))
    have hCount := cut.cross_num_edges _ _ hSecond hFirst
    have hPair : (data.sourceEnds edge).2 = left ∧ (data.sourceEnds edge).1 = right := by
      by_contra hNot
      have hZero := hCount.trans (ite_eq_right hNot)
      omega
    exact Or.inr (Prod.ext hPair.2 hPair.1)

/-- The distinguished old occurrence has the projected cut endpoints. -/
theorem old_sourceEnds_of_cut
    (candidate : BalancedGlobal.Candidate target degree data wall)
    {left right : candidate.datum.SourceVertex} (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left)) :
    data.sourceEnds edge = (sourceMap candidate left, sourceMap candidate right) ∨
      data.sourceEnds edge = (sourceMap candidate right, sourceMap candidate left) := by
  have hMap := sourceMap_oldSourceEdge_ends candidate edge
  rcases hEnds with hEnds | hEnds
  · rw [hEnds] at hMap
    exact Or.inl hMap.symm
  · rw [hEnds] at hMap
    exact Or.inr hMap.symm

/-- An occurrence crossing the image side lifts to an occurrence crossing
the original side, so it must be the distinguished retained occurrence. -/
theorem image_crossing_sourceEdge_eq
    (candidate : BalancedGlobal.Candidate target degree data wall)
    {left right : candidate.datum.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut candidate.datum.sourceGraph left right)
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left))
    {first second : data.SourceVertex}
    (hFirst : first ∈ imageSide candidate cut.side)
    (hSecond : second ∉ imageSide candidate cut.side)
    (other : data.SourceEdge)
    (hOther : data.sourceEnds other = (first, second) ∨ data.sourceEnds other = (second, first)) :
    other = edge := by
  apply oldSourceEdge_injective candidate
  apply crossing_sourceEdge_eq candidate.datum cut (candidate.oldSourceEdge edge) hEnds
  have hMap := sourceMap_oldSourceEdge_ends candidate other
  have hInside (vertex : candidate.datum.SourceVertex) (hEq : sourceMap candidate vertex = first) :
      vertex ∈ cut.side := by
    apply (sourceMap_mem_imageSide_iff candidate cut edge hEnds vertex).mp
    rwa [hEq]
  have hOutside (vertex : candidate.datum.SourceVertex) (hEq : sourceMap candidate vertex = second) :
      vertex ∉ cut.side := by
    intro hMem
    apply hSecond
    rw [← hEq]
    exact (sourceMap_mem_imageSide_iff candidate cut edge hEnds vertex).mpr hMem
  rcases hOther with hOther | hOther
  · rw [hOther] at hMap
    exact Or.inl ⟨hInside _ (congrArg Prod.fst hMap), hOutside _ (congrArg Prod.snd hMap)⟩
  · rw [hOther] at hMap
    exact Or.inr ⟨hInside _ (congrArg Prod.snd hMap), hOutside _ (congrArg Prod.fst hMap)⟩

/-- The image is an actual occurrence-safe separating cut of the old source.
This conclusion has no forest or genus hypothesis. -/
noncomputable def descendedCut
    (candidate : BalancedGlobal.Candidate target degree data wall)
    {left right : candidate.datum.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut candidate.datum.sourceGraph left right)
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left)) :
    Utilities.SeparatingEdgeCut data.sourceGraph (sourceMap candidate left) (sourceMap candidate right) := by
  classical
  have hLeft : sourceMap candidate left ∈ imageSide candidate cut.side :=
    (sourceMap_mem_imageSide_iff candidate cut edge hEnds left).mpr cut.left_mem
  have hRight : sourceMap candidate right ∉ imageSide candidate cut.side :=
    fun h ↦ cut.right_not_mem ((sourceMap_mem_imageSide_iff candidate cut edge hEnds right).mp h)
  refine { side := imageSide candidate cut.side
           left_mem := hLeft
           right_not_mem := hRight
           cross_num_edges := ?_ }
  intro first second hFirst hSecond
  have hOldEnds := old_sourceEnds_of_cut candidate edge hEnds
  have hPositions :
      (data.sourceEnds edge = (first, second) ∨ data.sourceEnds edge = (second, first)) ↔
        first = sourceMap candidate left ∧ second = sourceMap candidate right := by
    constructor
    · intro hPair
      rcases hOldEnds with hOldEnds | hOldEnds <;> rcases hPair with hPair | hPair
      all_goals have h := hOldEnds.symm.trans hPair
      · exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
      · have hWrong : sourceMap candidate right = first := congrArg Prod.snd h
        exact False.elim (hRight (hWrong.symm ▸ hFirst))
      · have hWrong : sourceMap candidate right = first := congrArg Prod.fst h
        exact False.elim (hRight (hWrong.symm ▸ hFirst))
      · exact ⟨(congrArg Prod.snd h).symm, (congrArg Prod.fst h).symm⟩
    · rintro ⟨rfl, rfl⟩
      exact hOldEnds
  rw [GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum data first second,
    Finset.sum_eq_single edge]
  · by_cases h : first = sourceMap candidate left ∧ second = sourceMap candidate right
    · exact (ite_eq_left (hPositions.mpr h)).trans (ite_eq_left h).symm
    · exact (ite_eq_right (fun hPair ↦ h (hPositions.mp hPair))).trans (ite_eq_right h).symm
  · intro other _ hOther
    apply ite_eq_right
    intro hCross
    exact hOther (image_crossing_sourceEdge_eq candidate cut edge hEnds hFirst hSecond other hCross)
  · simp

/-- The complementary side of the descended cut is connected in a connected
old source. No genus assertion enters this step. -/
theorem descendedCut_complement_connected
    (candidate : BalancedGlobal.Candidate target degree data wall) (hConnected : data.Connected)
    {left right : candidate.datum.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut candidate.datum.sourceGraph left right)
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left)) :
    graph_connected (Utilities.inducedSubgraph data.sourceGraph
      (Finset.univ \ (descendedCut candidate cut edge hEnds).side)
      ⟨sourceMap candidate right, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, (descendedCut candidate cut edge hEnds).right_not_mem⟩⟩) :=
  NonDanglingValency.complement_connected_of_unique_cross hConnected _
    (descendedCut candidate cut edge hEnds).right_not_mem
    (descendedCut candidate cut edge hEnds).cross_num_edges

/-- The chosen side is connected as well: apply the same unique-crossing
argument to the complementary cut. -/
theorem descendedCut_side_connected
    (candidate : BalancedGlobal.Candidate target degree data wall) (hConnected : data.Connected)
    {left right : candidate.datum.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut candidate.datum.sourceGraph left right)
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left)) :
    graph_connected (Utilities.inducedSubgraph data.sourceGraph
      (descendedCut candidate cut edge hEnds).side
      ⟨sourceMap candidate left, (descendedCut candidate cut edge hEnds).left_mem⟩) := by
  classical
  let down := descendedCut candidate cut edge hEnds
  have hOutside : sourceMap candidate left ∉ Finset.univ \ down.side := by
    intro h
    exact (Finset.mem_sdiff.mp h).2 down.left_mem
  have hCross : ∀ a b : data.SourceVertex,
      a ∈ Finset.univ \ down.side → b ∉ Finset.univ \ down.side →
      num_edges data.sourceGraph a b =
        if a = sourceMap candidate right ∧ b = sourceMap candidate left then 1 else 0 := by
    intro a b ha hb
    have haNot : a ∉ down.side := (Finset.mem_sdiff.mp ha).2
    have hbMem : b ∈ down.side := by
      by_contra h
      exact hb (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩)
    rw [num_edges_symmetric data.sourceGraph a b, down.cross_num_edges b a hbMem haNot]
    by_cases h : a = sourceMap candidate right ∧ b = sourceMap candidate left
    · exact (ite_eq_left h.symm).trans (ite_eq_left h).symm
    · exact (ite_eq_right (fun hPair ↦ h hPair.symm)).trans (ite_eq_right h).symm
  have hConnectedSide := NonDanglingValency.complement_connected_of_unique_cross
    hConnected (Finset.univ \ down.side) hOutside hCross
  simpa using hConnectedSide

end DraismaVargas.LocalCases.ResolutionCut
