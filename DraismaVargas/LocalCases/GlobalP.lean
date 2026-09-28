import DraismaVargas.LocalCases.GlobalMkk
import DraismaVargas.LocalCases.ResolutionP

/-!
# Global arbitrary-degree continuation in case P

Figure 35 of Draisma--Vargas Part I (Case `w2-r2-nd3-P`) merges a dangling
singleton into either of two endpoint blocks, or detaches it on the new edge.
Every new endpoint is divalent, so the global assembly is obtained from the
same guarded one-occurrence-per-side adapter as Case `w2-r2-nd3-M-kk`.
Equation (9) of Part I then provides the positive wall crossing.
-/

namespace DraismaVargas.LocalCases.GlobalP

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionP
open DraismaVargas.LocalCases.BalancingValencyTwo
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.GlobalMkk

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree} {wall : target.V}

/-- The two endpoint blocks and dangling singleton of source case P. -/
structure Geometry (data : GluingDatum target degree) (wall : target.V) where
  endpoint : SheetPartition degree
  first : Fin degree
  second : Fin degree
  extra : Fin degree
  endpoint_refines : endpoint.Refines (data.vertexPartition wall)
  first_second : ¬endpoint.Rel first second
  first_extra : ¬endpoint.Rel first extra
  second_extra : ¬endpoint.Rel second extra
  wall_first_second : (data.vertexPartition wall).Rel first second
  wall_first_extra : (data.vertexPartition wall).Rel first extra
  extraSingleton : endpoint.block extra = {extra}
  k₁ : ℕ
  k₂ : ℕ
  k₁_pos : 0 < k₁
  k₂_pos : 0 < k₂
  firstCard : endpoint.blockCard first = k₁
  secondCard : endpoint.blockCard second = k₂
  wallCard : (data.vertexPartition wall).blockCard first = k₁ + k₂ + 1

namespace Geometry

theorem wall_second_extra (geometry : Geometry data wall) :
    (data.vertexPartition wall).Rel geometry.second geometry.extra :=
  geometry.wall_first_second.symm.trans geometry.wall_first_extra

theorem extra_ne_first (geometry : Geometry data wall) :
    geometry.extra ≠ geometry.first := by
  intro h
  apply geometry.first_extra
  rw [h]
  rfl

/-- Figure 35, candidate 1: attach the singleton to the first block. -/
abbrev firstLocal (geometry : Geometry data wall) : LocalResolution degree :=
  attachedResolution (data.vertexPartition wall) geometry.endpoint
    geometry.first geometry.extra geometry.first_extra
    geometry.endpoint_refines geometry.wall_first_extra

/-- Figure 35, candidate 2: attach the singleton to the second block. -/
abbrev secondLocal (geometry : Geometry data wall) : LocalResolution degree :=
  attachedResolution (data.vertexPartition wall) geometry.endpoint
    geometry.second geometry.extra geometry.second_extra
    geometry.endpoint_refines geometry.wall_second_extra

/-- Figure 35, candidate 3: detach the singleton on the new edge. -/
abbrev thirdLocal (geometry : Geometry data wall) : LocalResolution degree :=
  residualResolution (data.vertexPartition wall) geometry.extra geometry.first
    geometry.extra_ne_first geometry.wall_first_extra.symm

end Geometry

/-- Contraction proof for candidate 1. -/
theorem firstLocal_contracts (geometry : Geometry data wall) :
    geometry.firstLocal.ContractsTo (data.vertexPartition wall) :=
  attachedResolution_contracts (data.vertexPartition wall) geometry.endpoint
    geometry.first geometry.extra geometry.first_extra geometry.endpoint_refines
    geometry.wall_first_extra

/-- Contraction proof for candidate 2. -/
theorem secondLocal_contracts (geometry : Geometry data wall) :
    geometry.secondLocal.ContractsTo (data.vertexPartition wall) :=
  attachedResolution_contracts (data.vertexPartition wall) geometry.endpoint
    geometry.second geometry.extra geometry.second_extra geometry.endpoint_refines
    geometry.wall_second_extra

/-- Contraction proof for candidate 3. -/
theorem thirdLocal_contracts (geometry : Geometry data wall) :
    geometry.thirdLocal.ContractsTo (data.vertexPartition wall) :=
  residualResolution_contracts (data.vertexPartition wall) geometry.extra
    geometry.first geometry.extra_ne_first geometry.wall_first_extra.symm

/-- The three actual arbitrary-degree Figure 35 candidates. -/
noncomputable def candidates (geometry : Geometry data wall)
    (first : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.firstLocal)
    (second : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.secondLocal)
    (third : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.thirdLocal) :
    Fin 3 → CertifiedCandidate data :=
  ![first.certified (firstLocal_contracts geometry),
    second.certified (secondLocal_contracts geometry),
    third.certified (thirdLocal_contracts geometry)]

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Equation (9) packaged with the three globally assembled candidates. -/
noncomputable def balancedFamily (geometry : Geometry data wall)
    (first : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.firstLocal)
    (second : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.secondLocal)
    (third : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.thirdLocal)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c₁ / ((geometry.k₁ : ℚ) + 1) + c₂ / (geometry.k₂ : ℚ) + s,
        c₁ / (geometry.k₁ : ℚ) + c₂ / ((geometry.k₂ : ℚ) + 1) + s,
        c₃ / ((geometry.k₁ : ℚ) + geometry.k₂) + s] i)
    (hleft : c₁ / (geometry.k₁ : ℚ) +
      c₂ / (geometry.k₂ : ℚ) + s = 0)
    (hright : c₃ / ((geometry.k₁ : ℚ) + geometry.k₂ + 1) + s = 0)
    (hAgree : ∀ i j,
      AgreeOffColumn (matrix i) (matrix j) wallColumn) :
    Family (coordinate := coordinate) 3 data where
  candidate := candidates geometry first second third
  matrix := matrix
  wallColumn := wallColumn
  weight := ![(geometry.k₁ : ℚ) + 1, (geometry.k₂ : ℚ) + 1,
    (geometry.k₁ : ℚ) + geometry.k₂]
  positiveBalance := by
    have hk₁ : (0 : ℚ) < (geometry.k₁ : ℚ) := by
      exact_mod_cast geometry.k₁_pos
    have hk₂ : (0 : ℚ) < (geometry.k₂ : ℚ) := by
      exact_mod_cast geometry.k₂_pos
    simpa only [hdet] using balance_P hk₁ hk₂ hleft hright
  agreeOffWall := hAgree

/-- Full arbitrary-degree continuation for source case P. -/
theorem exists_valid_positive_exit (geometry : Geometry data wall)
    (first : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.firstLocal)
    (second : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.secondLocal)
    (third : DivalentPattern (data := data) (wall := wall)
      geometry.first geometry.thirdLocal)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![c₁ / ((geometry.k₁ : ℚ) + 1) + c₂ / (geometry.k₂ : ℚ) + s,
        c₁ / (geometry.k₁ : ℚ) + c₂ / ((geometry.k₂ : ℚ) + 1) + s,
        c₃ / ((geometry.k₁ : ℚ) + geometry.k₂) + s] i)
    (hleft : c₁ / (geometry.k₁ : ℚ) +
      c₂ / (geometry.k₂ : ℚ) + s = 0)
    (hright : c₃ / ((geometry.k₁ : ℚ) + geometry.k₂ + 1) + s = 0)
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

end DraismaVargas.LocalCases.GlobalP
