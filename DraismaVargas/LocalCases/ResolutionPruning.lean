module

public import DraismaVargas.LocalCases.ResolutionSurvival

@[expose] public section

/-!
# Old dangling branches remain pruned in a genus-preserving resolution

The selected-fibre Euler defect is nonnegative. If total source genus is
preserved, every selected defect is zero. An old dangling cut therefore lifts
to a genuine genus-zero cut upstairs. Together with retained-edge survival,
this supplies the actual pruning equivalence needed by the M11 candidates.
-/

namespace DraismaVargas.LocalCases.ResolutionPruning

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 ResolutionCut ResolutionSideCounts W4StableSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

/-- The complete occurrence dictionary of an assembled resolution. -/
theorem sourceEdge_cases (candidate : BalancedGlobal.Candidate target degree data wall)
    (edge : candidate.datum.SourceEdge) :
    (∃ old : data.SourceEdge, edge = candidate.oldSourceEdge old) ∨
      ∃ sheet : Fin degree, edge = candidate.newSourceEdge sheet := by
  obtain ⟨label, hLabel⟩ := (occurrenceEquiv target wall candidate.right).surjective edge.1.1
  have hCanonical := (GluingDatum.sourceEdge_self candidate.datum edge).symm
  have hTarget := congrArg (fun place ↦ candidate.datum.sourceEdge place edge.1.2) hLabel.symm
  cases label with
  | none =>
      right
      refine ⟨edge.1.2, hCanonical.trans (hTarget.trans ?_)⟩
      exact sourceEdge_new data wall candidate.right
        (LocalResolution.paste _ candidate.resolution candidate.contracts)
        (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) edge.1.2
  | some old =>
      left
      refine ⟨data.sourceEdge old edge.1.2, hCanonical.trans (hTarget.trans ?_)⟩
      exact sourceEdge_old data wall candidate.right
        (LocalResolution.paste _ candidate.resolution candidate.contracts)
        (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) old edge.1.2

theorem sourceMap_newSourceEdge_ends (candidate : BalancedGlobal.Candidate target degree data wall)
    (sheet : Fin degree) :
    (sourceMap candidate (candidate.datum.sourceEnds (candidate.newSourceEdge sheet)).1,
      sourceMap candidate (candidate.datum.sourceEnds (candidate.newSourceEdge sheet)).2) =
      (data.sourceEndpoint wall sheet, data.sourceEndpoint wall sheet) :=
  sourceMap_new_ends data wall candidate.right
    (LocalResolution.paste _ candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior)
    (LocalResolution.paste_contracts _ _ _) sheet

noncomputable def liftedSide (candidate : BalancedGlobal.Candidate target degree data wall)
    (side : Finset data.SourceVertex) : Finset candidate.datum.SourceVertex :=
  preimageSide data wall candidate.right
    (LocalResolution.paste _ candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) side

@[simp] theorem mem_liftedSide (candidate : BalancedGlobal.Candidate target degree data wall)
    (side : Finset data.SourceVertex) (vertex : candidate.datum.SourceVertex) :
    vertex ∈ liftedSide candidate side ↔ sourceMap candidate vertex ∈ side :=
  mem_preimageSide data wall candidate.right
    (LocalResolution.paste _ candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) side vertex

/-- Only the retained distinguished occurrence can cross an old cut's full
preimage. New occurrences have identical projected endpoints. -/
theorem crossing_sourceEdge_eq
    (candidate : BalancedGlobal.Candidate target degree data wall)
    {left right : candidate.datum.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut data.sourceGraph (sourceMap candidate left) (sourceMap candidate right))
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left))
    (other : candidate.datum.SourceEdge)
    (hCross :
      (sourceMap candidate (candidate.datum.sourceEnds other).1 ∈ cut.side ∧
        sourceMap candidate (candidate.datum.sourceEnds other).2 ∉ cut.side) ∨
      (sourceMap candidate (candidate.datum.sourceEnds other).2 ∈ cut.side ∧
        sourceMap candidate (candidate.datum.sourceEnds other).1 ∉ cut.side)) :
    other = candidate.oldSourceEdge edge := by
  rcases sourceEdge_cases candidate other with ⟨old, rfl⟩ | ⟨sheet, rfl⟩
  · have hFirst : sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge old)).1 =
        (data.sourceEnds old).1 := congrArg Prod.fst (sourceMap_oldSourceEdge_ends candidate old)
    have hSecond : sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge old)).2 =
        (data.sourceEnds old).2 := congrArg Prod.snd (sourceMap_oldSourceEdge_ends candidate old)
    rw [hFirst, hSecond] at hCross
    exact congrArg candidate.oldSourceEdge
      (ResolutionCut.crossing_sourceEdge_eq data cut edge (old_sourceEnds_of_cut candidate edge hEnds) old hCross)
  · have hSame : sourceMap candidate (candidate.datum.sourceEnds (candidate.newSourceEdge sheet)).1 =
        sourceMap candidate (candidate.datum.sourceEnds (candidate.newSourceEdge sheet)).2 :=
      (congrArg Prod.fst (sourceMap_newSourceEdge_ends candidate sheet)).trans
        (congrArg Prod.snd (sourceMap_newSourceEdge_ends candidate sheet)).symm
    rw [hSame] at hCross
    rcases hCross with h | h <;> exact (h.2 h.1).elim

/-- The actual cut obtained by lifting an old separating side. Parallel
occurrences are handled through the complete source-edge dictionary. -/
noncomputable def liftedCut
    (candidate : BalancedGlobal.Candidate target degree data wall)
    {left right : candidate.datum.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut data.sourceGraph (sourceMap candidate left) (sourceMap candidate right))
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left)) :
    Utilities.SeparatingEdgeCut candidate.datum.sourceGraph left right := by
  classical
  have hLeft : left ∈ liftedSide candidate cut.side := (mem_liftedSide _ _ _).mpr cut.left_mem
  have hRight : right ∉ liftedSide candidate cut.side := fun h ↦ cut.right_not_mem ((mem_liftedSide _ _ _).mp h)
  refine { side := liftedSide candidate cut.side
           left_mem := hLeft
           right_not_mem := hRight
           cross_num_edges := ?_ }
  intro first second hFirst hSecond
  have hPositions :
      (candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (first, second) ∨
        candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (second, first)) ↔
      first = left ∧ second = right := by
    constructor
    · intro hPair
      rcases hEnds with hEnds | hEnds <;> rcases hPair with hPair | hPair
      all_goals have h := hEnds.symm.trans hPair
      · exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
      · have hWrong : right = first := congrArg Prod.snd h
        exact False.elim (hRight (hWrong.symm ▸ hFirst))
      · have hWrong : right = first := congrArg Prod.fst h
        exact False.elim (hRight (hWrong.symm ▸ hFirst))
      · exact ⟨(congrArg Prod.snd h).symm, (congrArg Prod.fst h).symm⟩
    · rintro ⟨rfl, rfl⟩
      exact hEnds
  rw [GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum candidate.datum first second,
    Finset.sum_eq_single (candidate.oldSourceEdge edge)]
  · by_cases h : first = left ∧ second = right
    · exact (ite_eq_left (hPositions.mpr h)).trans (ite_eq_left h).symm
    · exact (ite_eq_right (fun hPair ↦ h (hPositions.mp hPair))).trans (ite_eq_right h).symm
  · intro other _ hOther
    apply ite_eq_right
    intro hPair
    apply hOther
    apply crossing_sourceEdge_eq candidate cut edge hEnds other
    have hInside := (mem_liftedSide candidate cut.side first).mp hFirst
    have hOutside : sourceMap candidate second ∉ cut.side :=
      fun h ↦ hSecond ((mem_liftedSide candidate cut.side second).mpr h)
    rcases hPair with hPair | hPair <;> rw [hPair]
    · exact Or.inl ⟨hInside, hOutside⟩
    · exact Or.inr ⟨hInside, hOutside⟩
  · simp

theorem side_connected_of_cut {G : CFGraph} (hConnected : graph_connected G)
    {left right : G.V} (cut : Utilities.SeparatingEdgeCut G left right) :
    graph_connected (Utilities.inducedSubgraph G cut.side ⟨left, cut.left_mem⟩) := by
  classical
  have hOutside : left ∉ Finset.univ \ cut.side := by
    intro h
    exact (Finset.mem_sdiff.mp h).2 cut.left_mem
  have hCross : ∀ a b : G.V, a ∈ Finset.univ \ cut.side → b ∉ Finset.univ \ cut.side →
      num_edges G a b = if a = right ∧ b = left then 1 else 0 := by
    intro a b ha hb
    have haNot : a ∉ cut.side := (Finset.mem_sdiff.mp ha).2
    have hbMem : b ∈ cut.side := by
      by_contra h
      exact hb (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩)
    rw [num_edges_symmetric G a b, cut.cross_num_edges b a hbMem haNot]
    by_cases h : a = right ∧ b = left
    · exact (ite_eq_left h.symm).trans (ite_eq_left h).symm
    · exact (ite_eq_right (fun hPair ↦ h hPair.symm)).trans (ite_eq_right h).symm
  simpa using NonDanglingValency.complement_connected_of_unique_cross
    hConnected (Finset.univ \ cut.side) hOutside hCross

/-- Source-genus preservation makes the complete preimage of an old
genus-zero side genus zero as well, so the old dangling cut lifts literally. -/
noncomputable def liftedDanglingSide
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (hConnected : candidate.datum.Connected)
    (hGenus : genus candidate.datum.sourceGraph = genus data.sourceGraph)
    {left right : candidate.datum.SourceVertex}
    (dangling : DanglingSide data.sourceGraph (sourceMap candidate left) (sourceMap candidate right))
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left)) :
    DanglingSide candidate.datum.sourceGraph left right where
  toSeparatingEdgeCut := liftedCut candidate dangling.toSeparatingEdgeCut edge hEnds
  side_connected := side_connected_of_cut hConnected (liftedCut candidate dangling.toSeparatingEdgeCut edge hEnds)
  complement_connected := NonDanglingValency.complement_connected_of_unique_cross hConnected _
    (liftedCut candidate dangling.toSeparatingEdgeCut edge hEnds).right_not_mem
    (liftedCut candidate dangling.toSeparatingEdgeCut edge hEnds).cross_num_edges
  side_genus_zero := by
    have hCount := genus_side_eq_preimage data wall candidate.right
      (LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior)
      (LocalResolution.paste_contracts _ _ _) hGenus dangling.side ⟨sourceMap candidate left, dangling.left_mem⟩
    simpa only [liftedCut, liftedSide, BalancedGlobal.Candidate.datum, GlobalAssembly.datum] using
      hCount.symm.trans dangling.side_genus_zero

/-- Retaining an old dangling occurrence preserves its pruning status when
the resolution does not add source genus. -/
theorem isDangling_oldSourceEdge
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (hConnected : candidate.datum.Connected)
    (hGenus : genus candidate.datum.sourceGraph = genus data.sourceGraph)
    (edge : data.SourceEdge) (hDangling : IsDangling data edge) :
    IsDangling candidate.datum (candidate.oldSourceEdge edge) := by
  have hFirst : sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge edge)).1 =
      (data.sourceEnds edge).1 := congrArg Prod.fst (sourceMap_oldSourceEdge_ends candidate edge)
  have hSecond : sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge edge)).2 =
      (data.sourceEnds edge).2 := congrArg Prod.snd (sourceMap_oldSourceEdge_ends candidate edge)
  rcases hDangling with hDangling | hDangling
  · obtain ⟨dangling⟩ := hDangling
    have old : DanglingSide data.sourceGraph
        (sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge edge)).1)
        (sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge edge)).2) := by
      rw [hFirst, hSecond]
      exact dangling
    exact Or.inl ⟨liftedDanglingSide candidate hConnected hGenus old edge (Or.inl rfl)⟩
  · obtain ⟨dangling⟩ := hDangling
    have old : DanglingSide data.sourceGraph
        (sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge edge)).2)
        (sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge edge)).1) := by
      rw [hFirst, hSecond]
      exact dangling
    exact Or.inr ⟨liftedDanglingSide candidate hConnected hGenus old edge (Or.inr rfl)⟩

/-- An actual genus-preserving candidate has exactly the old pruning status
on every retained occurrence. No compatibility field is assumed. -/
theorem isDangling_oldSourceEdge_iff
    (candidate : BalancedGlobal.Candidate target degree data wall) (hValid : data.Valid)
    (hGenus : genus candidate.datum.sourceGraph = genus data.sourceGraph) (edge : data.SourceEdge) :
    IsDangling candidate.datum (candidate.oldSourceEdge edge) ↔ IsDangling data edge :=
  ⟨ResolutionSurvival.isDangling_of_oldSourceEdge candidate hValid.1 edge,
    isDangling_oldSourceEdge candidate (candidate.datum_valid hValid).1 hGenus edge⟩

end DraismaVargas.LocalCases.ResolutionPruning
