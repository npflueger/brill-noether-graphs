import DraismaVargas.LocalCases.GlobalM11Arbitrary
import DraismaVargas.LocalCases.ResolutionCoarseFine

/-!
# Global coarse/fine continuations for Equations (4) and (5)

These source cases have one divalent and one trivalent new endpoint.  The
shared `TrivalentPattern` exposes the only nonautomatic local obligation: the
three induced block counts at the trivalent endpoint.  It then installs the
selected resolution among arbitrary background wall blocks and constructs an
actual globally valid outgoing datum.

These are conditional partition/candidate APIs, not a derivation of the
source's two members. In particular `Nd2Geometry.fineLocal` places the fine
partition at the divalent endpoint. Figure 31's actual fine member instead
places it at the trivalent endpoint and keeps the ramification-one wall block
over the divalent large direction. Validity and genus preservation alone do
not justify using a same-side fine pattern in Equation (5), so a construction
of Figure 31's pair has to follow the figure's placement.
-/

namespace DraismaVargas.LocalCases.GlobalCoarseFine

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionM1k
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.BalancingRemaining
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.GlobalM11Arbitrary

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}

/-- Occurrence and induced-count input for a resolution with one old edge at
its divalent left endpoint and two old edges at its trivalent right endpoint. -/
structure TrivalentPattern (distinguished : Fin degree)
    (selected : LocalResolution degree) where
  background : Background data wall distinguished
  leftExternal : target.edges
  rightExternalFirst : target.edges
  rightExternalSecond : target.edges
  leftEdges : background.leftEdges = [leftExternal]
  rightEdges : background.rightEdges =
    [rightExternalFirst, rightExternalSecond]
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    (data.edgePartition edge).Refines
      (if background.right edge then selected.right else selected.left)
  rightCounts : ∀ anchor,
    (data.vertexPartition wall).Rel distinguished anchor →
    ∀ sheet, (data.vertexPartition wall).Rel anchor sheet →
      selected.newEdge.blockCountWithin selected.right sheet +
        (data.edgePartition rightExternalFirst).blockCountWithin
          selected.right sheet +
        (data.edgePartition rightExternalSecond).blockCountWithin
          selected.right sheet ≥ selected.right.blockCard sheet + 2

namespace TrivalentPattern

/-- Assemble a trivalent pattern with every nondistinguished wall block. -/
noncomputable def candidate {distinguished : Fin degree}
    {selected : LocalResolution degree}
    (pattern : TrivalentPattern (data := data) (wall := wall)
      distinguished selected)
    (hContracts : selected.ContractsTo (data.vertexPartition wall)) :
    Candidate target degree data wall := by
  apply pattern.background.install selected hContracts pattern.exterior
  · intro anchor _ _
    rw [pattern.leftEdges]
    simpa using riemannHurwitzAtBlock_divalent
      (data.vertexPartition wall) selected.left selected.newEdge
      (data.edgePartition pattern.leftExternal) anchor
  · intro anchor hRel _
    rw [pattern.rightEdges]
    exact riemannHurwitzAtBlock_trivalent_of_counts
      (data.vertexPartition wall) selected.right selected.newEdge
      (data.edgePartition pattern.rightExternalFirst)
      (data.edgePartition pattern.rightExternalSecond) anchor
      (pattern.rightCounts anchor hRel)

/-- A trivalent pattern as a heterogeneous global candidate. -/
noncomputable def certified {distinguished : Fin degree}
    {selected : LocalResolution degree}
    (pattern : TrivalentPattern (data := data) (wall := wall)
      distinguished selected)
    (hContracts : selected.ContractsTo (data.vertexPartition wall)) :
    CertifiedCandidate data := (pattern.candidate hContracts).certified

end TrivalentPattern

/-! ## Equation (4): `w3-r1-nd3-t3` -/

/-- The coarse wall block and its two-block refinement in Equation (4). -/
structure Nd3Geometry (data : GluingDatum target degree) (wall : target.V) where
  fine : SheetPartition degree
  first : Fin degree
  second : Fin degree
  fine_refines : fine.Refines (data.vertexPartition wall)
  wall_together : (data.vertexPartition wall).Rel first second
  fine_separate : ¬fine.Rel first second
  k₂ : ℕ
  k₃ : ℕ
  k₂_pos : 0 < k₂
  k₃_pos : 0 < k₃
  fineFirstCard : fine.blockCard first = k₂
  fineSecondCard : fine.blockCard second = k₃
  wallCard : (data.vertexPartition wall).blockCard first = k₂ + k₃

namespace Nd3Geometry

abbrev coarseLocal (_geometry : Nd3Geometry data wall) : LocalResolution degree :=
  thirdResolution (data.vertexPartition wall)

abbrev fineLocal (geometry : Nd3Geometry data wall) : LocalResolution degree :=
  fineResolution (data.vertexPartition wall) geometry.fine geometry.fine_refines

end Nd3Geometry

theorem nd3_coarse_contracts (geometry : Nd3Geometry data wall) :
    geometry.coarseLocal.ContractsTo (data.vertexPartition wall) :=
  thirdResolution_contracts (data.vertexPartition wall)

theorem nd3_fine_contracts (geometry : Nd3Geometry data wall) :
    geometry.fineLocal.ContractsTo (data.vertexPartition wall) :=
  fineResolution_contracts (data.vertexPartition wall) geometry.fine
    geometry.fine_refines

noncomputable def nd3Candidates (geometry : Nd3Geometry data wall)
    (coarse : TrivalentPattern (data := data) (wall := wall)
      geometry.first geometry.coarseLocal)
    (fine : TrivalentPattern (data := data) (wall := wall)
      geometry.first geometry.fineLocal) : Fin 2 → CertifiedCandidate data :=
  ![coarse.certified (nd3_coarse_contracts geometry),
    fine.certified (nd3_fine_contracts geometry)]

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Equation (4) packaged with its two actual global candidates. -/
noncomputable def nd3BalancedFamily (geometry : Nd3Geometry data wall)
    (coarse : TrivalentPattern (data := data) (wall := wall)
      geometry.first geometry.coarseLocal)
    (fine : TrivalentPattern (data := data) (wall := wall)
      geometry.first geometry.fineLocal)
    (matrix : Fin 2 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₂ c₃ c₄ s₃ s₄ : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c₄ / ((geometry.k₂ : ℚ) + geometry.k₃) + s₃,
        c₂ / (geometry.k₂ : ℚ) + c₃ / (geometry.k₃ : ℚ) + s₄] i)
    (h₃ : c₂ / (geometry.k₂ : ℚ) + c₃ / (geometry.k₃ : ℚ) + s₃ = 0)
    (h₄ : c₄ / ((geometry.k₂ : ℚ) + geometry.k₃) + s₄ = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 2 data where
  candidate := nd3Candidates geometry coarse fine
  matrix := matrix
  wallColumn := wallColumn
  weight := ![1, 1]
  positiveBalance := by
    simpa only [hdet] using balance_w3_nd3_t3 h₃ h₄
  agreeOffWall := hAgree

/-- Full arbitrary-degree continuation for Equation (4). -/
theorem nd3_exists_valid_positive_exit (geometry : Nd3Geometry data wall)
    (coarse : TrivalentPattern (data := data) (wall := wall)
      geometry.first geometry.coarseLocal)
    (fine : TrivalentPattern (data := data) (wall := wall)
      geometry.first geometry.fineLocal)
    (matrix : Fin 2 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₂ c₃ c₄ s₃ s₄ : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c₄ / ((geometry.k₂ : ℚ) + geometry.k₃) + s₃,
        c₂ / (geometry.k₂ : ℚ) + c₃ / (geometry.k₃ : ℚ) + s₄] i)
    (h₃ : c₂ / (geometry.k₂ : ℚ) + c₃ / (geometry.k₃ : ℚ) + s₃ = 0)
    (h₄ : c₄ / ((geometry.k₂ : ℚ) + geometry.k₃) + s₄ = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 2)
    (hincoming : (matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 2 → coordinate → ℚ)
    (hz : z wallColumn = 0)
    (hzpos : ∀ i, i ≠ wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (matrix incoming).mulVec incomingVelocity =
        (matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity wallColumn < 0) :
    ∃ outgoing,
      (nd3Candidates geometry coarse fine outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity := by
  exact (nd3BalancedFamily geometry coarse fine matrix wallColumn
    c₂ c₃ c₄ s₃ s₄ hdet h₃ h₄ hAgree).exists_valid_positive_exit
      hValid incoming hincoming z incomingVelocity outgoingVelocity hz hzpos
      (fun outgoing _ ↦ hSystems outgoing) hIncomingDirection

/-! ## Equation (5): `w3-r1-nd2` -/

/-- The coarse wall block and its residual fine block in Equation (5). -/
structure Nd2Geometry (data : GluingDatum target degree) (wall : target.V) where
  fine : SheetPartition degree
  anchor : Fin degree
  fine_refines : fine.Refines (data.vertexPartition wall)
  k : ℕ
  k_pos : 0 < k
  fineCard : fine.blockCard anchor = k
  wallCard : (data.vertexPartition wall).blockCard anchor = k + 1

namespace Nd2Geometry

abbrev coarseLocal (_geometry : Nd2Geometry data wall) : LocalResolution degree :=
  thirdResolution (data.vertexPartition wall)

abbrev fineLocal (geometry : Nd2Geometry data wall) : LocalResolution degree :=
  fineResolution (data.vertexPartition wall) geometry.fine geometry.fine_refines

end Nd2Geometry

theorem nd2_coarse_contracts (geometry : Nd2Geometry data wall) :
    geometry.coarseLocal.ContractsTo (data.vertexPartition wall) :=
  thirdResolution_contracts (data.vertexPartition wall)

theorem nd2_fine_contracts (geometry : Nd2Geometry data wall) :
    geometry.fineLocal.ContractsTo (data.vertexPartition wall) :=
  fineResolution_contracts (data.vertexPartition wall) geometry.fine
    geometry.fine_refines

noncomputable def nd2Candidates (geometry : Nd2Geometry data wall)
    (coarse : TrivalentPattern (data := data) (wall := wall)
      geometry.anchor geometry.coarseLocal)
    (fine : TrivalentPattern (data := data) (wall := wall)
      geometry.anchor geometry.fineLocal) : Fin 2 → CertifiedCandidate data :=
  ![coarse.certified (nd2_coarse_contracts geometry),
    fine.certified (nd2_fine_contracts geometry)]

/-- Equation (5) packaged with its two actual global candidates. -/
noncomputable def nd2BalancedFamily (geometry : Nd2Geometry data wall)
    (coarse : TrivalentPattern (data := data) (wall := wall)
      geometry.anchor geometry.coarseLocal)
    (fine : TrivalentPattern (data := data) (wall := wall)
      geometry.anchor geometry.fineLocal)
    (matrix : Fin 2 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c s₃ s₄ : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c / ((geometry.k : ℚ) + 1) + s₃,
        c / (geometry.k : ℚ) + s₄] i)
    (h₃ : c / (geometry.k : ℚ) + s₃ = 0)
    (h₄ : c / ((geometry.k : ℚ) + 1) + s₄ = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 2 data where
  candidate := nd2Candidates geometry coarse fine
  matrix := matrix
  wallColumn := wallColumn
  weight := ![1, 1]
  positiveBalance := by
    simpa only [hdet] using balance_w3_nd2 h₃ h₄
  agreeOffWall := hAgree

/-- Full arbitrary-degree continuation for Equation (5). -/
theorem nd2_exists_valid_positive_exit (geometry : Nd2Geometry data wall)
    (coarse : TrivalentPattern (data := data) (wall := wall)
      geometry.anchor geometry.coarseLocal)
    (fine : TrivalentPattern (data := data) (wall := wall)
      geometry.anchor geometry.fineLocal)
    (matrix : Fin 2 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c s₃ s₄ : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c / ((geometry.k : ℚ) + 1) + s₃,
        c / (geometry.k : ℚ) + s₄] i)
    (h₃ : c / (geometry.k : ℚ) + s₃ = 0)
    (h₄ : c / ((geometry.k : ℚ) + 1) + s₄ = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 2)
    (hincoming : (matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 2 → coordinate → ℚ)
    (hz : z wallColumn = 0)
    (hzpos : ∀ i, i ≠ wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (matrix incoming).mulVec incomingVelocity =
        (matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity wallColumn < 0) :
    ∃ outgoing,
      (nd2Candidates geometry coarse fine outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity := by
  exact (nd2BalancedFamily geometry coarse fine matrix wallColumn
    c s₃ s₄ hdet h₃ h₄ hAgree).exists_valid_positive_exit
      hValid incoming hincoming z incomingVelocity outgoingVelocity hz hzpos
      (fun outgoing _ ↦ hSystems outgoing) hIncomingDirection

end DraismaVargas.LocalCases.GlobalCoarseFine
