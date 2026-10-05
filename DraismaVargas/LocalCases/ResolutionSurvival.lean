module

public import DraismaVargas.LocalCases.ResolutionSideCounts

@[expose] public section

/-!
# Retained source occurrences survive a literal wall resolution

A hypothetical dangling side upstairs descends to an actual separating cut
downstairs by `ResolutionCut`. Its induced genus cannot increase under the
contraction, by the selected-block Euler count in `ResolutionSideCounts`.
Connectedness makes that genus nonnegative, hence zero. Contraposition proves
survival of every retained old survivor, without a forest or an assumed
danglingness-compatibility field.
-/

namespace DraismaVargas.LocalCases.ResolutionSurvival

open DraismaVargas.Infrastructure
open ResolutionM11 ResolutionCut ResolutionSideCounts W4StableSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

/-- The genus of the actual descended cut side is bounded by the original
side's genus, with saturation derived from its retained crossing occurrence. -/
theorem genus_descendedCut_le
    (candidate : BalancedGlobal.Candidate target degree data wall)
    {left right : candidate.datum.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut candidate.datum.sourceGraph left right)
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left)) :
    genus (Utilities.inducedSubgraph data.sourceGraph
      (descendedCut candidate cut edge hEnds).side
      ⟨sourceMap candidate left, (descendedCut candidate cut edge hEnds).left_mem⟩) ≤
      genus (Utilities.inducedSubgraph candidate.datum.sourceGraph cut.side ⟨left, cut.left_mem⟩) := by
  classical
  let resolution := LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts
  let compatible := GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
    candidate.contracts candidate.exterior
  have hSide : (imageSide candidate cut.side).Nonempty :=
    ⟨sourceMap candidate left, (sourceMap_mem_imageSide_iff candidate cut edge hEnds left).mpr cut.left_mem⟩
  have hPreimage : preimageSide data wall candidate.right resolution compatible
      (imageSide candidate cut.side) = cut.side := by
    ext vertex
    simp only [preimageSide, Finset.mem_filter, Finset.mem_univ, true_and]
    exact sourceMap_mem_imageSide_iff candidate cut edge hEnds vertex
  have hGenus := genus_side_le_preimage data wall candidate.right resolution compatible
    (LocalResolution.paste_contracts _ _ _) (imageSide candidate cut.side) hSide
  simpa only [hPreimage, descendedCut, resolution, compatible,
    BalancedGlobal.Candidate.datum, GlobalAssembly.datum] using hGenus

/-- Descend a genuine dangling side through a retained source occurrence.
The genus-zero field is proved from the induced-side Euler inequality. -/
noncomputable def descendedDanglingSide
    (candidate : BalancedGlobal.Candidate target degree data wall) (hConnected : data.Connected)
    {left right : candidate.datum.SourceVertex}
    (dangling : DanglingSide candidate.datum.sourceGraph left right)
    (edge : data.SourceEdge)
    (hEnds : candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (left, right) ∨
      candidate.datum.sourceEnds (candidate.oldSourceEdge edge) = (right, left)) :
    DanglingSide data.sourceGraph (sourceMap candidate left) (sourceMap candidate right) where
  toSeparatingEdgeCut := descendedCut candidate dangling.toSeparatingEdgeCut edge hEnds
  side_connected := descendedCut_side_connected candidate hConnected dangling.toSeparatingEdgeCut edge hEnds
  complement_connected := descendedCut_complement_connected candidate hConnected dangling.toSeparatingEdgeCut edge hEnds
  side_genus_zero := by
    have hLe := genus_descendedCut_le candidate dangling.toSeparatingEdgeCut edge hEnds
    have hNonneg := Utilities.genus_nonneg_of_graph_connected _
      (descendedCut_side_connected candidate hConnected dangling.toSeparatingEdgeCut edge hEnds)
    have hZero := dangling.side_genus_zero
    omega

/-- If a retained occurrence is dangling after resolution, it was already
dangling before resolution. Both orientations of its genus-zero side count. -/
theorem isDangling_of_oldSourceEdge
    (candidate : BalancedGlobal.Candidate target degree data wall) (hConnected : data.Connected)
    (edge : data.SourceEdge) (hDangling : IsDangling candidate.datum (candidate.oldSourceEdge edge)) :
    IsDangling data edge := by
  have hFirst : sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge edge)).1 =
      (data.sourceEnds edge).1 := congrArg Prod.fst (sourceMap_oldSourceEdge_ends candidate edge)
  have hSecond : sourceMap candidate (candidate.datum.sourceEnds (candidate.oldSourceEdge edge)).2 =
      (data.sourceEnds edge).2 := congrArg Prod.snd (sourceMap_oldSourceEdge_ends candidate edge)
  rcases hDangling with hDangling | hDangling
  · obtain ⟨dangling⟩ := hDangling
    left
    have down := descendedDanglingSide candidate hConnected dangling edge (Or.inl rfl)
    rw [hFirst, hSecond] at down
    exact ⟨down⟩
  · obtain ⟨dangling⟩ := hDangling
    right
    have down := descendedDanglingSide candidate hConnected dangling edge (Or.inr rfl)
    rw [hFirst, hSecond] at down
    exact ⟨down⟩

/-- Every old non-dangling occurrence remains non-dangling in the actual
candidate. This is independent of the local case and of source-genus equality. -/
theorem not_isDangling_oldSourceEdge
    (candidate : BalancedGlobal.Candidate target degree data wall) (hConnected : data.Connected)
    (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge) :
    ¬ IsDangling candidate.datum (candidate.oldSourceEdge edge) :=
  fun hDangling ↦ hSurvives (isDangling_of_oldSourceEdge candidate hConnected edge hDangling)

end DraismaVargas.LocalCases.ResolutionSurvival
