import DraismaVargas.Infrastructure.TargetSeparation
import DraismaVargas.LocalCases.GlobalM11Arbitrary
import DraismaVargas.LocalCases.ResolutionM1k

/-!
# Global arbitrary-degree continuation in case M-1k

This file installs the three Figure 33 resolutions on one wall block of size
`k + 1`, while arbitrary independently classified resolutions occupy every
other wall block.  The resulting objects are actual occurrence-labelled
global gluing data.  Equation (7) then gives a valid positive exit through the
common length wall.

## Two versions of the family, and which one an actual profile can use

`candidates` and `exists_valid_positive_exit` put all three Figure 33 members
over **one** `data` and one `Geometry`.  That is the shape the equation needs,
but it is **not instantiable at an actual `w2M1k` source profile**:
`W2M1kSourceCandidates.no_common_geometry` derives `False` from a
`FirstPattern` and a `SecondPattern` over one `Geometry`, because `M⁽¹⁾` forces
the two wall directions' pinned sheets equal and `M⁽²⁾` forces them distinct.
Both requirements come from the `FirstPattern`/`SecondPattern` fields declared
here, so the obstruction lies in this file's single-datum packaging and not in
Part I.

The remedy is the one `GlobalM11Arbitrary` already uses for Figure 32: a branch
swap along one wall branch exchanges the two situations, so the second member
may live over the **branch-swapped** datum.  The section
*The branch-swapped second member* below mirrors
`GlobalM11Arbitrary.SwappedDatum` / `remoteCertified` for M-1k:
`swappedCandidates`, `swappedBalancedFamily` and
`exists_valid_positive_exit_swapped` are the versions an actual profile can
instantiate.  The single-datum family is kept alongside them because it is the
literal reading of Figure 33 and is what the balance identity
`BalancingValencyTwo.balance_M_1k` is stated against.

`Infrastructure.TargetSeparation` is imported for that section: it is what tells
a caller that the swap across one wall occurrence leaves the other wall
occurrence alone (`TargetSeparation.edgeMoved_eq_false`), which is the
hypothesis `W2M1kSourceCandidates.branchSwap_aligns` carries as `hSeparated`.
-/

namespace DraismaVargas.LocalCases.GlobalM1k

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionM1k
open DraismaVargas.LocalCases.BalancingValencyTwo
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.GlobalM11Arbitrary

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}

/-- The selected `1,k` wall block, including a third sheet witnessing that
the residual `k - 1` block in candidate 2 is nonempty. -/
structure Geometry (data : GluingDatum target degree) (wall : target.V) where
  first : Fin degree
  second : Fin degree
  third : Fin degree
  first_second : (data.vertexPartition wall).Rel first second
  first_third : (data.vertexPartition wall).Rel first third
  first_ne_second : first ≠ second
  first_ne_third : first ≠ third
  second_ne_third : second ≠ third
  k : ℕ
  one_lt_k : 1 < k
  blockCard : (data.vertexPartition wall).blockCard first = k + 1

namespace Geometry

/-- Figure 33, candidate 1, on the selected block. -/
abbrev firstLocal (geometry : Geometry data wall) : LocalResolution degree :=
  firstResolution (data.vertexPartition wall) geometry.first geometry.second
    geometry.first_ne_second geometry.first_second

/-- Figure 33, candidate 2, on the selected block. -/
abbrev secondLocal (geometry : Geometry data wall) : LocalResolution degree :=
  secondResolution (data.vertexPartition wall) geometry.first geometry.second
    geometry.third geometry.first_second geometry.first_third
    geometry.first_ne_second geometry.first_ne_third geometry.second_ne_third

/-- Figure 33, candidate 3, on the selected block. -/
abbrev thirdLocal (_geometry : Geometry data wall) : LocalResolution degree :=
  thirdResolution (data.vertexPartition wall)

end Geometry

/-- Occurrence and exterior-refinement input for Figure 33, candidate 1. -/
structure FirstPattern (geometry : Geometry data wall) where
  background : Background data wall geometry.first
  firstExternal : target.edges
  secondExternal : target.edges
  leftEdges : background.leftEdges = []
  rightEdges : background.rightEdges = [firstExternal, secondExternal]
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    (data.edgePartition edge).Refines
      (if background.right edge then geometry.firstLocal.right
        else geometry.firstLocal.left)

namespace FirstPattern

/-- Candidate 1 assembled with all nondistinguished wall blocks. -/
noncomputable def candidate (geometry : Geometry data wall)
    (pattern : FirstPattern geometry) : Candidate target degree data wall := by
  apply pattern.background.install geometry.firstLocal
    (firstResolution_contracts (data.vertexPartition wall) geometry.first
      geometry.second geometry.first_ne_second geometry.first_second)
    pattern.exterior
  · intro anchor _ _
    rw [pattern.leftEdges]
    simpa using LocalResolution.riemannHurwitzAtBlock_leaf
      (data.vertexPartition wall) geometry.firstLocal.left
      geometry.firstLocal.newEdge anchor
  · intro anchor hRel _
    rw [pattern.rightEdges]
    simpa using firstResolution_right_riemannHurwitzAtBlock_of_rel
      (data.vertexPartition wall) (data.edgePartition pattern.firstExternal)
      (data.edgePartition pattern.secondExternal) geometry.first
      geometry.second anchor geometry.first_ne_second geometry.first_second hRel

/-- Candidate 1 as a heterogeneous global candidate. -/
noncomputable def certified (geometry : Geometry data wall)
    (pattern : FirstPattern geometry) : CertifiedCandidate data :=
  (pattern.candidate geometry).certified

end FirstPattern

/-- Occurrence and exterior-refinement input for Figure 33, candidate 2. -/
structure SecondPattern (geometry : Geometry data wall) where
  background : Background data wall geometry.first
  leftExternal : target.edges
  rightExternal : target.edges
  leftEdges : background.leftEdges = [leftExternal]
  rightEdges : background.rightEdges = [rightExternal]
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    (data.edgePartition edge).Refines
      (if background.right edge then geometry.secondLocal.right
        else geometry.secondLocal.left)

namespace SecondPattern

/-- Candidate 2 assembled with all nondistinguished wall blocks. -/
noncomputable def candidate (geometry : Geometry data wall)
    (pattern : SecondPattern geometry) : Candidate target degree data wall := by
  apply pattern.background.install geometry.secondLocal
    (secondResolution_contracts (data.vertexPartition wall) geometry.first
      geometry.second geometry.third geometry.first_second geometry.first_third
      geometry.first_ne_second geometry.first_ne_third geometry.second_ne_third)
    pattern.exterior
  · intro anchor _ _
    rw [pattern.leftEdges]
    simpa using riemannHurwitzAtBlock_divalent
      (data.vertexPartition wall) geometry.secondLocal.left
      geometry.secondLocal.newEdge (data.edgePartition pattern.leftExternal)
      anchor
  · intro anchor _ _
    rw [pattern.rightEdges]
    simpa using riemannHurwitzAtBlock_divalent
      (data.vertexPartition wall) geometry.secondLocal.right
      geometry.secondLocal.newEdge (data.edgePartition pattern.rightExternal)
      anchor

/-- Candidate 2 as a heterogeneous global candidate. -/
noncomputable def certified (geometry : Geometry data wall)
    (pattern : SecondPattern geometry) : CertifiedCandidate data :=
  (pattern.candidate geometry).certified

end SecondPattern

/-- Occurrence and exterior-refinement input for Figure 33, candidate 3. -/
structure ThirdPattern (geometry : Geometry data wall) where
  background : Background data wall geometry.first
  leftExternal : target.edges
  rightExternal : target.edges
  leftEdges : background.leftEdges = [leftExternal]
  rightEdges : background.rightEdges = [rightExternal]
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    (data.edgePartition edge).Refines
      (if background.right edge then geometry.thirdLocal.right
        else geometry.thirdLocal.left)

namespace ThirdPattern

/-- Candidate 3 assembled with all nondistinguished wall blocks. -/
noncomputable def candidate (geometry : Geometry data wall)
    (pattern : ThirdPattern geometry) : Candidate target degree data wall := by
  apply pattern.background.install geometry.thirdLocal
    (thirdResolution_contracts (data.vertexPartition wall)) pattern.exterior
  · intro anchor _ _
    rw [pattern.leftEdges]
    simpa using thirdResolution_left_riemannHurwitzAtBlock
      (data.vertexPartition wall) (data.edgePartition pattern.leftExternal)
      anchor
  · intro anchor _ _
    rw [pattern.rightEdges]
    simpa using thirdResolution_right_riemannHurwitzAtBlock
      (data.vertexPartition wall) (data.edgePartition pattern.rightExternal)
      anchor

/-- Candidate 3 as a heterogeneous global candidate. -/
noncomputable def certified (geometry : Geometry data wall)
    (pattern : ThirdPattern geometry) : CertifiedCandidate data :=
  (pattern.candidate geometry).certified

end ThirdPattern

/-- The three actual arbitrary-degree Figure 33 candidates. -/
noncomputable def candidates (geometry : Geometry data wall)
    (first : FirstPattern geometry) (second : SecondPattern geometry)
    (third : ThirdPattern geometry) : Fin 3 → CertifiedCandidate data :=
  ![first.certified geometry, second.certified geometry,
    third.certified geometry]

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Equation (7) packaged with the three globally assembled candidates. -/
noncomputable def balancedFamily (geometry : Geometry data wall)
    (first : FirstPattern geometry) (second : SecondPattern geometry)
    (third : ThirdPattern geometry)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![2 * c₁,
        c₁ + c₂ / ((geometry.k : ℚ) - 1) + s,
        c₃ / ((geometry.k : ℚ) + 1) + s] i)
    (hleft : c₁ + c₂ / (geometry.k : ℚ) + s = 0)
    (hright : c₃ / (geometry.k : ℚ) + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 3 data where
  candidate := candidates geometry first second third
  matrix := matrix
  wallColumn := wallColumn
  weight := ![1, 2 * ((geometry.k : ℚ) - 1),
    2 * ((geometry.k : ℚ) + 1)]
  positiveBalance := by
    have hk : (1 : ℚ) < (geometry.k : ℚ) := by
      exact_mod_cast geometry.one_lt_k
    simpa only [hdet] using balance_M_1k hk hleft hright
  agreeOffWall := hAgree

/-- Full arbitrary-degree continuation for source case M-1k: choose a valid
opposite-sign global candidate and step a positive rational distance into its
length cone. -/
theorem exists_valid_positive_exit (geometry : Geometry data wall)
    (first : FirstPattern geometry) (second : SecondPattern geometry)
    (third : ThirdPattern geometry)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![2 * c₁,
        c₁ + c₂ / ((geometry.k : ℚ) - 1) + s,
        c₃ / ((geometry.k : ℚ) + 1) + s] i)
    (hleft : c₁ + c₂ / (geometry.k : ℚ) + s = 0)
    (hright : c₃ / (geometry.k : ℚ) + s = 0)
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
      (candidates geometry first second third outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity := by
  exact (balancedFamily geometry first second third matrix wallColumn
    c₁ c₂ c₃ s hdet hleft hright hAgree).exists_valid_positive_exit
      hValid incoming hincoming z incomingVelocity outgoingVelocity hz hzpos
      (fun outgoing _ ↦ hSystems outgoing) hIncomingDirection

/-! ## The branch-swapped second member

Figure 33's three members cannot share one gluing datum (see the module
docstring).  What follows is the M-1k mirror of
`GlobalM11Arbitrary.SwappedDatum` / `GlobalM11Arbitrary.remoteCertified`: the
second member is taken over the datum branch-swapped across one wall branch,
and is still certified **against the original datum**, because the branch swap
preserves validity.
-/

section Swapped

/-- The branch swap fixes the wall partition as a term: the wall vertex is
outside the moved branch.  This is `W3FourDisjointness`'s
`branchSwapOfPerm_vertexPartition_wall` at a transposition, proved locally so
that `GlobalM1k` does not acquire a dependency on that file. -/
theorem swappedDatum_vertexPartition_wall (root : target.V) (hRoot : root ≠ wall)
    (p q : Fin degree) (hTogether : (data.vertexPartition wall).Rel p q) :
    (SwappedDatum data wall root hRoot p q hTogether).vertexPartition wall =
      data.vertexPartition wall := by
  change (data.vertexPartition wall).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.vertexMoved wall root hRoot wall) (Equiv.swap p q)) = _
  rw [TargetBranchRegion.vertexMoved_wall]
  cases hPartition : data.vertexPartition wall
  rfl

/-- The selected `1,k` wall block of the branch-swapped datum is the selected
block of the original one: every field of `Geometry` speaks about the wall
partition only, and the swap fixes it. -/
def Geometry.swapped (geometry : Geometry data wall) (root : target.V)
    (hRoot : root ≠ wall) (p q : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel p q) :
    Geometry (SwappedDatum data wall root hRoot p q hTogether) wall where
  first := geometry.first
  second := geometry.second
  third := geometry.third
  first_second := by
    rw [swappedDatum_vertexPartition_wall]
    exact geometry.first_second
  first_third := by
    rw [swappedDatum_vertexPartition_wall]
    exact geometry.first_third
  first_ne_second := geometry.first_ne_second
  first_ne_third := geometry.first_ne_third
  second_ne_third := geometry.second_ne_third
  k := geometry.k
  one_lt_k := geometry.one_lt_k
  blockCard := by
    rw [swappedDatum_vertexPartition_wall]
    exact geometry.blockCard

theorem Geometry.swapped_k (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall) (p q : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel p q) :
    (geometry.swapped root hRoot p q hTogether).k = geometry.k := rfl

/-- **The remote second member.**  Candidate 2 assembled over the
branch-swapped datum is still a globally valid candidate *for the original
datum*: the branch swap preserves validity
(`ResolutionM11.wallBranchSwap_preserves_valid`), and blockwise assembly then
preserves it again.  This is `GlobalM11Arbitrary.remoteCertified` for
Figure 33. -/
noncomputable def SecondPattern.remoteCertified (root : target.V)
    (hRoot : root ≠ wall) (p q : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel p q)
    (geometry : Geometry (SwappedDatum data wall root hRoot p q hTogether) wall)
    (pattern : SecondPattern geometry) : CertifiedCandidate data where
  outgoingTarget := TargetExpansion.graph target wall pattern.background.right
  datum := (pattern.candidate geometry).datum
  valid_of_old := by
    intro hValid
    exact (pattern.candidate geometry).datum_valid
      (wallBranchSwap_preserves_valid data hValid wall root hRoot p q hTogether)

/-- The three actual arbitrary-degree Figure 33 candidates, with the second
member over the branch-swapped datum.  Members one and three keep the original
datum, exactly as in `GlobalM11Arbitrary.candidates`. -/
noncomputable def swappedCandidates (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall) (p q : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel p q)
    (first : FirstPattern geometry)
    (second : SecondPattern (geometry.swapped root hRoot p q hTogether))
    (third : ThirdPattern geometry) : Fin 3 → CertifiedCandidate data :=
  ![first.certified geometry,
    SecondPattern.remoteCertified root hRoot p q hTogether
      (geometry.swapped root hRoot p q hTogether) second,
    third.certified geometry]

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Equation (7) packaged with the three globally assembled candidates, the
second one remote.  The balance identity is the same `balance_M_1k`: the
determinant hypotheses are stated about the members, and which datum a member
lives over does not enter the identity. -/
noncomputable def swappedBalancedFamily (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall) (p q : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel p q)
    (first : FirstPattern geometry)
    (second : SecondPattern (geometry.swapped root hRoot p q hTogether))
    (third : ThirdPattern geometry)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![2 * c₁,
        c₁ + c₂ / ((geometry.k : ℚ) - 1) + s,
        c₃ / ((geometry.k : ℚ) + 1) + s] i)
    (hleft : c₁ + c₂ / (geometry.k : ℚ) + s = 0)
    (hright : c₃ / (geometry.k : ℚ) + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 3 data where
  candidate := swappedCandidates geometry root hRoot p q hTogether first second third
  matrix := matrix
  wallColumn := wallColumn
  weight := ![1, 2 * ((geometry.k : ℚ) - 1),
    2 * ((geometry.k : ℚ) + 1)]
  positiveBalance := by
    have hk : (1 : ℚ) < (geometry.k : ℚ) := by
      exact_mod_cast geometry.one_lt_k
    simpa only [hdet] using balance_M_1k hk hleft hright
  agreeOffWall := hAgree

/-- **Full arbitrary-degree continuation for source case M-1k, with the second
member over the branch-swapped datum.**  This is the form an actual `w2M1k`
profile can instantiate; `exists_valid_positive_exit` above cannot be, because
its `FirstPattern` and `SecondPattern` over one `Geometry` are jointly
contradictory (`W2M1kSourceCandidates.no_common_geometry`).

*Why this hypothesis bundle is jointly satisfiable.*  The obstruction is
entirely in the two `exterior` fields: over one datum `M⁽¹⁾`'s forces the two
wall directions to isolate the same sheet and `M⁽²⁾`'s forces them to isolate
different ones.  Here `first` reads `data.edgePartition` and `second` reads
`(SwappedDatum …).edgePartition`, which differ exactly on the branch swapped
across -- `W2M1kSourceCandidates.branchSwap_aligns` and `branchSwap_separates`
are the statements that a swap carries either exterior condition to the other,
on a datum that stays valid (`branchSwapped_valid`).  So a profile that
satisfies `M⁽¹⁾` on its own datum satisfies `M⁽²⁾` on the swapped one, and
conversely.  Everything else in the bundle is about the matrices and is
independent of which datum a member lives over.

This declaration provides the *slot*; it does not itself build the two
patterns at a `w2M1k` profile.  That construction belongs with the profile:
`W2M1kSwapped` builds both from one aligned profile
(`W2M1kSwapped.nonempty_swappedBundle`). -/
theorem exists_valid_positive_exit_swapped (geometry : Geometry data wall)
    (root : target.V) (hRoot : root ≠ wall) (p q : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel p q)
    (first : FirstPattern geometry)
    (second : SecondPattern (geometry.swapped root hRoot p q hTogether))
    (third : ThirdPattern geometry)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![2 * c₁,
        c₁ + c₂ / ((geometry.k : ℚ) - 1) + s,
        c₃ / ((geometry.k : ℚ) + 1) + s] i)
    (hleft : c₁ + c₂ / (geometry.k : ℚ) + s = 0)
    (hright : c₃ / (geometry.k : ℚ) + s = 0)
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
      (swappedCandidates geometry root hRoot p q hTogether first second third
        outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity := by
  exact (swappedBalancedFamily geometry root hRoot p q hTogether first second third
    matrix wallColumn c₁ c₂ c₃ s hdet hleft hright hAgree).exists_valid_positive_exit
      hValid incoming hincoming z incomingVelocity outgoingVelocity hz hzpos
      (fun outgoing _ ↦ hSystems outgoing) hIncomingDirection

end Swapped

end DraismaVargas.LocalCases.GlobalM1k
