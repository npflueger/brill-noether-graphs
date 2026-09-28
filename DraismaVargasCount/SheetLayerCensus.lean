import DraismaVargasCount.DiagonalTargetIso

/-!
# The partition census over the diagonal target layer

A diagonal open odd member of the caterpillar fibre whose core diagonal is the ballot
diagonal of `s` is isomorphic to the ballot family member at `s` as soon as
`DiagonalTargetIso.SheetLayerSupply` holds: the five sheet fields of a `GeometricDatumIso`
between the ballot family member at `s` and the diagonal member, over the
target layer `DiagonalTargetIso.targetLayer` (constructed outright).  Matching every
vertex and edge partition up to a permutation does **not** give an isomorphism
(`DiagonalTargetIso.census_not_sufficient`): the permutations must be compatible
along every edge, which is a global matching.

This file fixes the interface between the two halves.

* `PartitionCensus m request` -- over the target layer, every vertex partition and
  every edge partition of the member is a relabelling of the ballot member's.
  (The vertex clause over interior spine vertices is
  `DiagonalTargetIso.spine_vertexPartition_relabel`; the leaf case is `LeafFibre`.
  The census is proved in `PartitionCensusProof`.)
* The global half is `PartitionCensus m request → SheetLayerSupply m request`,
  proved in `SheetLayerMatching`.

`PartitionCensus` is implied by `SheetLayerSupply` (take the layer's
permutations), and together with the global matching it is equivalent to it; it is
strictly weaker in general (`DiagonalTargetIso.census_not_sufficient`, over an
arbitrary pair of data).

## What is NOT proved here

Neither `PartitionCensus` nor the implication to `SheetLayerSupply`; only
`partitionCensus_of_sheetLayerSupply`.
-/

namespace DraismaVargas.Count.SheetLayerCensus

open DraismaVargas.Count.DiagonalTargetIso
open DraismaVargas.Count.FibreCaterpillar (catCore)

/-- **The partition census** at every diagonal open odd member whose core diagonal is
a ballot sequence's, over `targetLayer`. -/
def PartitionCensus (m : ℕ) (request : Fin (6 * m + 3) → ℚ) : Prop :=
  ∀ (s : Slopes (2 * (m + 1))) (mem : FibreMember (catCore m) request (m + 2)),
    mem.Open → mem.HasOddMult → ∀ hD : mem.Diagonal,
      mem.coreDiag = BallotSlopes.ballotCoreDiag m s →
        (∀ v, ∃ π, mem.data.vertexPartition
            ((targetLayer (BallotCoreIdentification.ballotFamilyMember m request s) mem
              (RigidityBasepoint.ballotFamilyMember_diagonal m request s) hD).targetVertex v) =
          ((BallotCoreIdentification.ballotFamilyMember m request s).data.vertexPartition v).relabel
            π) ∧
        (∀ e, ∃ π, mem.data.edgePartition
            ((targetLayer (BallotCoreIdentification.ballotFamilyMember m request s) mem
              (RigidityBasepoint.ballotFamilyMember_diagonal m request s) hD).targetEdge e) =
          ((BallotCoreIdentification.ballotFamilyMember m request s).data.edgePartition e).relabel
            π)

/-- The census is necessary (the easy direction). -/
theorem partitionCensus_of_sheetLayerSupply {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (h : SheetLayerSupply m request) : PartitionCensus m request := by
  intro s mem hOpen hOdd hD hdiag
  obtain ⟨L⟩ := h s mem hOpen hOdd hD hdiag
  exact ⟨fun v ↦ ⟨L.vertexPerm v, L.vertexPartition v⟩,
    fun e ↦ ⟨L.edgePerm e, L.edgePartition e⟩⟩

end DraismaVargas.Count.SheetLayerCensus
