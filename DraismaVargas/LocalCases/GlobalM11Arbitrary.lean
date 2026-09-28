import DraismaVargas.LocalCases.BalancedGlobal

/-!
# The M-11 resolution inside an arbitrary-degree wall

Figure 32 only changes one two-sheet block of the wall partition.  The other
wall blocks carry independent local resolutions.  This file installs that
distinguished M-11 block in the blockwise global assembly, without restricting
the ambient degree to two.

`Background` records exactly the receipts owed by the other wall blocks.  Its
conditions are deliberately guarded by separation from `distinguished`; the
M-11 constructors below discharge contraction and Riemann--Hurwitz on the
distinguished block themselves.  Consequently this is not a degree-two model
embedded by an assumption: it produces an actual arbitrary-degree outgoing
gluing datum.
-/

namespace DraismaVargas.LocalCases.GlobalM11Arbitrary

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancingValencyTwo

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}

/-- Blockwise resolution receipts away from one distinguished wall block. -/
structure Background (data : GluingDatum target degree) (wall : target.V)
    (distinguished : Fin degree) where
  right : target.edges → Bool
  resolution : Fin degree → LocalResolution degree
  contracts : ∀ anchor,
    ¬(data.vertexPartition wall).Rel distinguished anchor →
      (resolution anchor).ContractsTo (data.vertexPartition wall)
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    ∀ anchor, ¬(data.vertexPartition wall).Rel distinguished anchor →
      (data.edgePartition edge).Refines
        (if right edge then (resolution anchor).right
          else (resolution anchor).left)
  leftEdges : List target.edges
  rightEdges : List target.edges
  leftEdges_eq : (leftEdges : Multiset target.edges) =
    (wallEdgesAssigned target wall right false).val
  rightEdges_eq : (rightEdges : Multiset target.edges) =
    (wallEdgesAssigned target wall right true).val
  left_riemannHurwitz : ∀ anchor,
    (data.vertexPartition wall).repr anchor = anchor →
    ¬(data.vertexPartition wall).Rel distinguished anchor →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        (resolution anchor).left
        ((resolution anchor).newEdge ::
          leftEdges.map data.edgePartition) anchor
  right_riemannHurwitz : ∀ anchor,
    (data.vertexPartition wall).repr anchor = anchor →
    ¬(data.vertexPartition wall).Rel distinguished anchor →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        (resolution anchor).right
        ((resolution anchor).newEdge ::
          rightEdges.map data.edgePartition) anchor

namespace Background

variable {distinguished : Fin degree}

/-- Replace the missing distinguished-block receipt by one prescribed local
resolution.  All fields of `Candidate` are then genuine derived receipts. -/
noncomputable def install (background : Background data wall distinguished)
    (selected : LocalResolution degree)
    (hContracts : selected.ContractsTo (data.vertexPartition wall))
    (hExterior : ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) →
      (data.edgePartition edge).Refines
        (if background.right edge then selected.right else selected.left))
    (hLeft : ∀ anchor,
      (data.vertexPartition wall).Rel distinguished anchor →
      (data.vertexPartition wall).repr anchor = anchor →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        selected.left
        (selected.newEdge :: background.leftEdges.map data.edgePartition)
        anchor)
    (hRight : ∀ anchor,
      (data.vertexPartition wall).Rel distinguished anchor →
      (data.vertexPartition wall).repr anchor = anchor →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        selected.right
        (selected.newEdge :: background.rightEdges.map data.edgePartition)
        anchor) :
    Candidate target degree data wall where
  right := background.right
  resolution := LocalResolution.onBlock (data.vertexPartition wall)
    distinguished selected background.resolution
  contracts := by
    intro anchor
    by_cases hRel : (data.vertexPartition wall).Rel distinguished anchor
    · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hRel]
      exact hContracts
    · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRel]
      exact background.contracts anchor hRel
  exterior := by
    intro edge hIncident anchor
    by_cases hRel : (data.vertexPartition wall).Rel distinguished anchor
    · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hRel]
      exact (hExterior edge hIncident).refinesOnBlock anchor
    · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRel]
      exact (background.exterior edge hIncident anchor hRel).refinesOnBlock
        anchor
  leftEdges := background.leftEdges
  rightEdges := background.rightEdges
  leftEdges_eq := background.leftEdges_eq
  rightEdges_eq := background.rightEdges_eq
  left_riemannHurwitz := by
    intro anchor hCanonical
    by_cases hRel : (data.vertexPartition wall).Rel distinguished anchor
    · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hRel]
      exact hLeft anchor hRel hCanonical
    · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRel]
      exact background.left_riemannHurwitz anchor hCanonical hRel
  right_riemannHurwitz := by
    intro anchor hCanonical
    by_cases hRel : (data.vertexPartition wall).Rel distinguished anchor
    · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hRel]
      exact hRight anchor hRel hCanonical
    · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hRel]
      exact background.right_riemannHurwitz anchor hCanonical hRel

/-- Install either split M-11 candidate on the distinguished two-sheet block.
The empty/paired occurrence lists are the valency-two incidence pattern of
Figure 32; the selected block's two endpoint inequalities are automatic. -/
noncomputable def splitCandidate
    (background : Background data wall distinguished)
    (_hCard : (data.vertexPartition wall).blockCard distinguished = 2)
    (first second : target.edges)
    (hLeftEdges : background.leftEdges = [])
    (hRightEdges : background.rightEdges = [first, second])
    (hExterior : ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) →
      (data.edgePartition edge).Refines
        (if background.right edge then
          (splitResolutionAt (data.vertexPartition wall) distinguished).right
        else (splitResolutionAt
          (data.vertexPartition wall) distinguished).left)) :
    Candidate target degree data wall := by
  apply background.install
    (splitResolutionAt (data.vertexPartition wall) distinguished)
    (splitResolutionAt_contracts _ _) hExterior
  · intro anchor _ _
    rw [hLeftEdges]
    simpa using LocalResolution.riemannHurwitzAtBlock_leaf
      (data.vertexPartition wall)
      (splitResolutionAt (data.vertexPartition wall) distinguished).left
      (splitResolutionAt (data.vertexPartition wall) distinguished).newEdge
      anchor
  · intro anchor hRel _
    rw [hRightEdges]
    simpa using splitResolutionAt_right_riemannHurwitzAtBlock_of_rel
      (data.vertexPartition wall) (data.edgePartition first)
      (data.edgePartition second) distinguished anchor hRel

/-- Install the joined M-11 candidate on the distinguished two-sheet block.
Each endpoint is divalent, so positivity of block counts proves its selected
block Riemann--Hurwitz inequalities for arbitrary exterior partitions. -/
noncomputable def joinedCandidate
    (background : Background data wall distinguished)
    (_hCard : (data.vertexPartition wall).blockCard distinguished = 2)
    (left rightEdge : target.edges)
    (hLeftEdges : background.leftEdges = [left])
    (hRightEdges : background.rightEdges = [rightEdge])
    (hExterior : ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) →
      (data.edgePartition edge).Refines
        (if background.right edge then
          (joinedResolutionAt (data.vertexPartition wall)).right
        else (joinedResolutionAt (data.vertexPartition wall)).left)) :
    Candidate target degree data wall := by
  apply background.install
    (joinedResolutionAt (data.vertexPartition wall))
    (joinedResolutionAt_contracts _) hExterior
  · intro anchor _ _
    rw [hLeftEdges]
    simpa using joinedResolutionAt_endpoint_riemannHurwitzAtBlock_any
      (data.vertexPartition wall) (data.edgePartition left) anchor
  · intro anchor _ _
    rw [hRightEdges]
    simpa [joinedResolutionAt] using
      joinedResolutionAt_endpoint_riemannHurwitzAtBlock_any
        (data.vertexPartition wall) (data.edgePartition rightEdge) anchor

end Background

/-! ## The three arbitrary-degree M-11 candidates -/

/-- Complete occurrence-level input for one of the two split candidates. -/
structure SplitPattern (data : GluingDatum target degree) (wall : target.V)
    (distinguished : Fin degree) where
  background : Background data wall distinguished
  blockCard : (data.vertexPartition wall).blockCard distinguished = 2
  first : target.edges
  second : target.edges
  leftEdges : background.leftEdges = []
  rightEdges : background.rightEdges = [first, second]
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    (data.edgePartition edge).Refines
      (if background.right edge then
        (splitResolutionAt (data.vertexPartition wall) distinguished).right
      else (splitResolutionAt
        (data.vertexPartition wall) distinguished).left)

namespace SplitPattern

variable {distinguished : Fin degree}

/-- The actual arbitrary-degree outgoing split datum, assembled over every
wall block. -/
noncomputable def candidate
    (pattern : SplitPattern data wall distinguished) :
    Candidate target degree data wall :=
  pattern.background.splitCandidate pattern.blockCard pattern.first
    pattern.second pattern.leftEdges pattern.rightEdges pattern.exterior

/-- The split datum as a heterogeneous globally valid candidate. -/
noncomputable def certified
    (pattern : SplitPattern data wall distinguished) :
    CertifiedCandidate data := pattern.candidate.certified

end SplitPattern

/-- Complete occurrence-level input for the joined candidate. -/
structure JoinedPattern (data : GluingDatum target degree) (wall : target.V)
    (distinguished : Fin degree) where
  background : Background data wall distinguished
  blockCard : (data.vertexPartition wall).blockCard distinguished = 2
  left : target.edges
  rightEdge : target.edges
  leftEdges : background.leftEdges = [left]
  rightEdges : background.rightEdges = [rightEdge]
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    (data.edgePartition edge).Refines
      (if background.right edge then
        (joinedResolutionAt (data.vertexPartition wall)).right
      else (joinedResolutionAt (data.vertexPartition wall)).left)

namespace JoinedPattern

variable {distinguished : Fin degree}

/-- The actual arbitrary-degree outgoing joined datum, assembled over every
wall block. -/
noncomputable def candidate
    (pattern : JoinedPattern data wall distinguished) :
    Candidate target degree data wall :=
  pattern.background.joinedCandidate pattern.blockCard pattern.left
    pattern.rightEdge pattern.leftEdges pattern.rightEdges pattern.exterior

/-- The joined datum as a heterogeneous globally valid candidate. -/
noncomputable def certified
    (pattern : JoinedPattern data wall distinguished) :
    CertifiedCandidate data := pattern.candidate.certified

end JoinedPattern

variable {distinguished other : Fin degree}

/-- The remote relabelling which distinguishes the second split candidate. -/
abbrev SwappedDatum (data : GluingDatum target degree) (wall root : target.V)
    (hRoot : root ≠ wall) (distinguished other : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel distinguished other) :=
  (wallBranchSwap data wall root hRoot distinguished other hTogether).apply

/-- A split pattern over the remotely relabelled contracted datum gives a
globally valid candidate relative to the original datum: branch relabelling
first preserves validity, then blockwise assembly does. -/
noncomputable def remoteCertified
    (root : target.V) (hRoot : root ≠ wall)
    (_hDifferent : distinguished ≠ other)
    (hTogether : (data.vertexPartition wall).Rel distinguished other)
    (pattern : SplitPattern
      (SwappedDatum data wall root hRoot distinguished other hTogether)
      wall distinguished) :
    CertifiedCandidate data where
  outgoingTarget := TargetExpansion.graph target wall
    pattern.background.right
  datum := pattern.candidate.datum
  valid_of_old := by
    intro hValid
    apply pattern.candidate.datum_valid
    exact wallBranchSwap_preserves_valid data hValid wall root hRoot
      distinguished other hTogether

/-- The two split candidates (the second after remote sheet transport) and
the joined candidate, at arbitrary ambient degree. -/
noncomputable def candidates
    (root : target.V) (hRoot : root ≠ wall)
    (hDifferent : distinguished ≠ other)
    (hTogether : (data.vertexPartition wall).Rel distinguished other)
    (first : SplitPattern data wall distinguished)
    (second : SplitPattern
      (SwappedDatum data wall root hRoot distinguished other hTogether)
      wall distinguished)
    (third : JoinedPattern data wall distinguished) :
    Fin 3 → CertifiedCandidate data :=
  ![first.certified,
    remoteCertified root hRoot hDifferent hTogether second,
    third.certified]

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Equation (6) attached to the actual arbitrary-degree M-11 candidates.
The remaining hypotheses are precisely the occurrence-specific length-matrix
identities and the two Kirchhoff relations from the paper. -/
noncomputable def balancedFamily
    (root : target.V) (hRoot : root ≠ wall)
    (hDifferent : distinguished ≠ other)
    (hTogether : (data.vertexPartition wall).Rel distinguished other)
    (first : SplitPattern data wall distinguished)
    (second : SplitPattern
      (SwappedDatum data wall root hRoot distinguished other hTogether)
      wall distinguished)
    (third : JoinedPattern data wall distinguished)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i,
      (matrix i).det = ![2 * c₁, 2 * c₂, c₃ / 2 + s] i)
    (hleft : c₁ + c₂ + s = 0) (hright : c₃ + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 3 data where
  candidate := candidates root hRoot hDifferent hTogether first second third
  matrix := matrix
  wallColumn := wallColumn
  weight := ![1, 1, 4]
  positiveBalance := by
    simpa only [hdet] using balance_M_11 hleft hright
  agreeOffWall := hAgree

/-- Any nondegenerate arbitrary-degree M-11 member has an actual globally
valid member on the opposite side of the determinant wall. -/
theorem exists_valid_opposite
    (root : target.V) (hRoot : root ≠ wall)
    (hDifferent : distinguished ≠ other)
    (hTogether : (data.vertexPartition wall).Rel distinguished other)
    (first : SplitPattern data wall distinguished)
    (second : SplitPattern
      (SwappedDatum data wall root hRoot distinguished other hTogether)
      wall distinguished)
    (third : JoinedPattern data wall distinguished)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i,
      (matrix i).det = ![2 * c₁, 2 * c₂, c₃ / 2 + s] i)
    (hleft : c₁ + c₂ + s = 0) (hright : c₃ + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 3)
    (hincoming : (matrix incoming).det ≠ 0) :
    ∃ outgoing,
      (candidates root hRoot hDifferent hTogether first second third
        outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 := by
  exact (balancedFamily root hRoot hDifferent hTogether first second third matrix
    wallColumn c₁ c₂ c₃ s hdet hleft hright hAgree).exists_valid_opposite
      hValid incoming hincoming

/-- Full cone-wall continuation for the arbitrary-degree M-11 family.  Given
compatible incoming/outgoing length systems, it chooses a globally valid
opposite-sign candidate and a positive rational step into its cone. -/
theorem exists_valid_positive_exit
    (root : target.V) (hRoot : root ≠ wall)
    (hDifferent : distinguished ≠ other)
    (hTogether : (data.vertexPartition wall).Rel distinguished other)
    (first : SplitPattern data wall distinguished)
    (second : SplitPattern
      (SwappedDatum data wall root hRoot distinguished other hTogether)
      wall distinguished)
    (third : JoinedPattern data wall distinguished)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i,
      (matrix i).det = ![2 * c₁, 2 * c₂, c₃ / 2 + s] i)
    (hleft : c₁ + c₂ + s = 0) (hright : c₃ + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 3)
    (hincoming : (matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 3 → coordinate → ℚ)
    (hz : z wallColumn = 0)
    (hzpos : ∀ i, i ≠ wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (matrix incoming).mulVec incomingVelocity =
        (matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity wallColumn < 0) :
    ∃ outgoing,
      (candidates root hRoot hDifferent hTogether first second third
        outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity := by
  exact (balancedFamily root hRoot hDifferent hTogether first second third
    matrix wallColumn c₁ c₂ c₃ s hdet hleft hright hAgree).exists_valid_positive_exit
      hValid incoming hincoming z incomingVelocity outgoingVelocity hz hzpos
      (fun outgoing _ ↦ hSystems outgoing) hIncomingDirection

end DraismaVargas.LocalCases.GlobalM11Arbitrary
